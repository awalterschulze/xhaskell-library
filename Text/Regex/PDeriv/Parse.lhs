> {-# LANGUAGE FlexibleContexts #-}
> module Text.Regex.PDeriv.Parse (parsePat, parsePatPosix) where

> {- By Kenny Zhuo Ming Lu and Martin Sulzmann, 2009. BSD3 -}

The parser that parse POSIX style regex syntax and translate it into our 
internal pattern representation.
This parser is largely adapted from Text.Regex.TDFA.ReadRegex

> import Data.Char
> import Text.ParserCombinators.Parsec((<|>), (<?>),
>                                      unexpected, try, runParser, many, getState, setState, CharParser, ParseError,
>                                      sepBy1, option, notFollowedBy, many1, lookAhead, eof, between,
>                                      string, oneOf, noneOf, digit, char, anyChar)
> import Control.Monad(liftM, when, guard)
> import Data.List (sort,nub)
> import qualified Data.IntMap as IM
> import qualified Data.ByteString.Char8 as S

> import Text.Regex.PDeriv.ExtPattern (EPat(..))
> import Text.Regex.PDeriv.IntPattern (Pat(..))
> import Text.Regex.PDeriv.RE (RE(..))
> import Text.Regex.PDeriv.Translate (translate, translatePosix) 

> type EState = ()
> initEState = ()

> -- | Return either a parse error or an external pattern
> parseEPat :: String -> Either ParseError (EPat, EState)
> parseEPat x = runParser (do { pat <- p_ere
>                             ; eof
>                             ; state <- getState
>                             ; return (pat,state)
>                             } ) initEState x x

> parsePat :: String -> Either ParseError Pat
> parsePat x = case parseEPat x of
>              { Left error -> Left error
>              ; Right (epat, estate) -> Right (translate epat)
>              }

posix pattern parsing: we need to add binders everywhere

> parsePatPosix :: String -> Either ParseError (Pat,IM.IntMap ())
> parsePatPosix x = case parseEPat x of
>                   { Left error -> Left error
>                   ; Right (epat, estate) -> Right (translatePosix epat)
>                   }


> p_ere :: CharParser EState EPat
> p_ere = liftM EOr $ sepBy1 p_branch (char '|')

> p_branch :: CharParser EState EPat
> p_branch = liftM EConcat $ many1 p_exp

> p_exp = (p_anchor <|> p_atom) >>= p_post_anchor_or_atom
>         
> p_anchor = ((char '^') >> (return ECarat))       -- '^'
>            <|>
>            ((char '$') >> (return EDollar))      -- '$'

todo '{'

> p_atom = p_group <|>
>          p_charclass <|>
>          p_dot <|>
>          p_esc_char <|>
>          p_char

 p_group = liftM EGroup $ between (char '(') (char ')') p_ere

> p_group = 
>     between (char '(') (char ')') 
>                 ( try 
>                   ( do  
>                     { -- non marking group 
>                     ; (char '?') 
>                     ; (char ':')
>                     ; x <- p_ere
>                     ; return (EGroupNonMarking x)
>                     } 
>                   )
>                  <|>
>                  liftM EGroup p_ere
>                 )



parsing [ ... ] and [^ ... ]

> p_charclass = 
>     (char '[') 
>     >> ( do { char '^' 
>             ; liftM ENoneOf $ p_enum -- enum ends with ']'
>             } 
>          <|>
>          (liftM EAny $ p_enum)
>        )

> p_enum :: CharParser EState [Char]
> p_enum = do { initial <- (option "" ((char ']' >> return "]") <|> (char '-' >> return "-"))) 
>               -- todo : why do we need this here? 
>               -- answer: if not, this string can't be parsed "[]f-z]", which is any char of  ']' and  between 'f' to 'z'
>             ; chars <- many1 p_one_enum
>             ; char ']'
>             ; let chars_set = nub (sort (initial ++ (concat chars)))
>             ; return chars_set
>             }

todo: support the locale collating char class [: :] [= =] [. .]

> p_one_enum = p_range <|> p_char_set 

> p_range = try $ do  
>           { start <- (try p_esc_char_) <|> noneOf "]-"
>           ; char '-'
>           ; end <- (try p_esc_char_) <|> noneOf "]"
>           ; return [ start .. end ] 
>           }

> p_char_set = do 
>   { c <- (try p_esc_char_) <|> noneOf "]" -- <|> (char '\\' >> p_special_char)
>   ; when (c == '-') $
>     do -- when it is a dash, it must be at the end of the [..]
>     { atEnd <- (lookAhead (char ']') >> return True) <|> (return False)
>     ; when (not atEnd) (unexpected "A dash is in the wrong place in a bracket")
>     }
>   ; return [c]
>   }

parse the dot (all characters)

> p_dot = char '.' >> (return EDot)

parse the escaped chars

> p_esc_char_ = char '\\' >> ((try p_tab) <|> (try p_return) <|> (try p_newline) <|> (try p_oct_ascii) <|> anyChar)

> p_esc_char = char '\\' >> ((try p_tab) <|> (try p_return) <|> (try p_newline) <|> (try p_oct_ascii) <|> anyChar) >>= \c -> return (EEscape c)

oct ascii, e.g. \000

> p_return = do 
>            { char 'r'
>            ; return '\r'
>            }

> p_newline = do 
>             { char 'n'
>             ; return '\n'
>             }

> p_tab = do 
>         { char 't'
>         ; return '\t'
>         }


> p_oct_ascii = do  
>               { d1 <- digit
>               ; d2 <- digit
>               ; d3 <- digit
>               ; return (chr ((digitToInt d2)*8 + (digitToInt d3)))
>               }


parse a single non-escaped char

> specials = "^.[$()|*+?{\\"

> p_char = noneOf specials >>= \c -> return (EChar c)

> p_special_char :: CharParser EState Char
> p_special_char = oneOf specials


> p_post_anchor_or_atom atom = 
>     (try (char '?' >> char '?' >> return (EOpt atom False)) <|> (char '?' >> return (EOpt atom True)))
>     <|> (try (char '+' >> char '?' >> return (EPlus atom False)) <|> (char '+' >> return (EPlus atom True)))
>     <|> (try (char '*' >> char '?' >> return (EStar atom False)) <|> (char '*' >> return (EStar atom True)))
>     <|> p_bound_nongreedy atom
>     <|> p_bound atom 
>     <|> return atom


> p_bound_nongreedy atom = try $ between (string "{") (string "}?") (p_bound_spec atom False)

> p_bound atom = try $ between (char '{') (char '}') (p_bound_spec atom True)

> p_bound_spec atom b = do { lowS <- many1 digit
>                         ; let lowI = read lowS
>                         ; highMI <- option (Just lowI) $ try $ 
>                           do { char ','
>  -- parsec note: if 'many digits' fails below then the 'try' ensures
>  -- that the ',' will not match the closing '}' in p_bound, same goes
>  -- for any non '}' garbage after the 'many digits'.
>                              ; highS <- many digit
>                              ; if null highS then return Nothing -- no upper bound
>                                else do { let highI = read highS
>                                        ; guard (lowI <= highI)
>                                        ; return (Just (read highS))
>                                        }
>                              }
>                         ; return (EBound atom lowI highMI b)
>                         }



