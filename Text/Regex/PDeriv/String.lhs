> {- By Kenny Zhuo Ming Lu and Martin Sulzmann, 2009, BSD License -}

A string implementation of reg exp pattern matching using partial derivative

> {-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances, TypeSynonymInstances, FlexibleContexts #-} 


> module Text.Regex.PDeriv.String 
>     ( Regex
>     , CompOption(..)
>     , ExecOption(..)
>     , defaultCompOpt
>     , defaultExecOpt
>     , compile
>     , execute
>     , regexec
>     ) where 

The re-exports

> import Text.Regex.PDeriv.String.LeftToRightD ( Regex
>                                              , CompOption(..)
>                                              , ExecOption(..)
>                                              , defaultCompOpt
>                                              , defaultExecOpt
>                                              , compile
>                                              , execute
>                                              , regexec
>                                              ) 

