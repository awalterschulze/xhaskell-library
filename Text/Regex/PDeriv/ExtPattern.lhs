> module Text.Regex.PDeriv.ExtPattern where

> -- | The external pattern syntax (ERE syntax)
> data EPat = EEmpty 
>          | EGroup EPat    -- ^ the group ( re )
>          | EOr [EPat]     -- ^ the union re|re
>          | EConcat [EPat] -- ^ the concantenation rere
>          | EOpt EPat      -- ^ the option re?
>          | EPlus EPat     -- ^ the plus re+
>          | EStar EPat     -- ^ the star re*
>          | EBound EPat Int (Maybe Int) -- ^ re{1:10}
>          | ECarat         -- ^ the ^ NOTE:shouldn't this must be top level?
>          | EDollar        -- ^ the $
>          | EDot           -- ^ the any char .
>          | EAny [Char]    -- ^ the character class [ a-z ] 
>          | ENoneOf [Char] -- ^ the negative character class [^a-z]
>          | EEscape Char   -- ^ backslash char
>          | EChar Char     -- ^ the non-escaped char
>           deriving Show

