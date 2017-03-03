all: transpile test

transpile:
	pcal2tla *tla

test:
	tlc *tla
