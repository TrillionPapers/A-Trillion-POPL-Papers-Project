# Runs the calculus of the paper on random tasks, tests its theorems on them, and regenerates
# the numbers that the paper quotes.  `make check` needs python3 and nothing else.  `make graph`
# extracts the import graph of Lean's library again and needs a Lean toolchain (elan); the
# committed lean-imports.txt is that of Lean 4.36.0.
.PHONY: all check graph clean

all: check

check:
	mkdir -p out
	python3 merge.py out > /dev/null
	diff -u expected/check.txt out/check.txt
	diff -u expected/numbers.tex out/numbers.tex

graph:
	python3 imports.py lean-imports.txt

clean:
	rm -rf out __pycache__
