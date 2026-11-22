# Runs the model of the paper on three small batches and on random ones, compares its criteria
# with running the calls in every order, and regenerates the numbers and the table rows that
# the paper quotes.  `make check` fails if any of them differs from the files in expected/,
# which the paper reads.  Needs python3 and nothing else.
.PHONY: all check clean

FILES = check.txt numbers.tex kinds.tex

all: check

check:
	mkdir -p out
	python3 batch.py out > /dev/null
	for f in $(FILES); do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
