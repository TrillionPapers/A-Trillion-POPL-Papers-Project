# Runs the model of the paper on a small example and on random contexts, compares the minimum
# cut and the other analyses with a search over all sets of kept items, and regenerates the
# numbers and the table rows that the paper quotes.  `make check` fails if any of them differs
# from the files in expected/, which the paper reads.  Needs python3 and nothing else.
.PHONY: all check clean

FILES = check.txt numbers.tex example.tex rules.tex patience.tex

all: check

check:
	mkdir -p out
	python3 compact.py out > /dev/null
	for f in $(FILES); do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
