.PHONY: run test setup bench

test: 
	stack test

test-trace:
	stack test --trace

bench:
	stack bench

build:
	stack build
	
setup:
	stack setup

ide-setup:
	stack build intero

install-haddock:
	stack install haddock-2.17.2

lint:
	hlint .

pkg:
	stack sdist
	echo "Now upload the created file to: https://hackage.haskell.org/upload"
