all: process test

process:
	pcal2tla *tla

test:
	tlc *tla
