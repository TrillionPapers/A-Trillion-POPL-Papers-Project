# Checks the artifact of the paper. Needs Lean 4 through elan; the version is in lean-toolchain.
LEAN ?= lean

.PHONY: all check measure clean

all: check measure

# Theorems of Sections 2 to 4. Fails if Lean reports an error or if the axioms differ.
check:
	mkdir -p out
	$(LEAN) Audit.lean > out/check.txt
	diff -u expected/check.txt out/check.txt

# Numbers of Section 5. The paper includes numbers.tex and the two tables, so its numbers are
# the output of Measure.lean. Fails if a new run gives different files.
measure:
	mkdir -p out
	$(LEAN) Measure.lean > out/measure.txt
	diff -u expected/measure.txt out/measure.txt
	diff -u numbers.tex out/numbers.tex
	diff -u table-sizes.tex out/table-sizes.tex
	diff -u table-examples.tex out/table-examples.tex

clean:
	rm -rf out
