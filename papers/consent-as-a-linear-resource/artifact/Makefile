# Runs the calculus of the paper on random programs, tests its theorems on them, and
# regenerates the numbers that the paper quotes.  Needs python3 and nothing else.
.PHONY: all check clean

all: check

check:
	mkdir -p out
	python3 consent.py out > /dev/null
	diff -u expected/check.txt out/check.txt
	diff -u expected/numbers.tex out/numbers.tex

clean:
	rm -rf out __pycache__
