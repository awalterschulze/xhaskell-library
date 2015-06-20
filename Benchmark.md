# Benchmarks #

In this page, we compare the performance of xhaskell-library with other implementations using a few examples.

  * `Text.Regex.PDeriv, Text.Regex.PDeriv.TwoPasses, Tex.Regex.PDeriv.Reverse` are three different matching approaches we provide in our library.
  * `Text.Regex.Posix` is the "default" library in currently shipped with GHC.
  * `Text.Regex.PCRE` is a [wrapper of the C PCRE library](http://hackage.haskell.org/package/regex-pcre-builtin).
  * `Text.Regex.PCRELight` is a [light-weight wrapper of the C PCRE library](http://hackage.haskell.org/package/pcre-light-0.3.1).
  * `Text.Regex.TDFA` is a [regular expression library](http://hackage.haskell.org/package/regex-tdfa) that implements of [TRE](http://www.laurikari.net/tre/).

The tests are conducted on a Macbook Core2Duo 2.4GHZ machine with 4GRam.
The time/memory usage are measured using the GHC runtime flag `+RTS -sstderr -RTS`

## The US Address Pattern ##

In this example, we use regex to extract the US addresses from an address book file.
The pattern will match address in format of
```
<ADDRESS> <STATE CODE> <ZIP CODE>
```
e.g. Mountain View, CA 90410.

The address book file we used in this example  is available in the [download](http://code.google.com/p/xhaskell-library/downloads/list) session. Note that the addresses listed in this file are artificially generated.

|Text.Regex.PDeriv.ByteString.LeftToRight|Text.Regex.PDeriv.ByteString.TwoPasses|Tex.Regex.PDeriv.ByteString.RightToLeft|Text.Regex.Posix|Text.Regex.PCRE|Text.Regex.PCRELight|Text.Regex.TDFA|Text.Regex.Parsec|
|:---------------------------------------|:-------------------------------------|:--------------------------------------|:---------------|:--------------|:-------------------|:--------------|:----------------|
|4.64s/32MB                              |2.44s/32MB                            |1.70s/32MB                             |19.31s/48MB     |1.85s/52MB     |272.80s/45MB        |18.86s/16MB    |40.36s/32MB      |
