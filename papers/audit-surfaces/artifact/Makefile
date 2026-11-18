# Checks the artifact of the paper. Needs Lean 4 through elan; the version is in lean-toolchain.
LEAN ?= lean

.PHONY: all check measure clean

all: check measure

# Theorems of Sections 2 to 4. Fails if Lean reports an error or if the axioms differ.
check:
	$(LEAN) Audit.lean > check.out
	diff -u expected/check.txt check.out

# Numbers of Section 5. Fails if they differ from the numbers the paper reports.
measure:
	$(LEAN) Measure.lean > measure.out
	diff -u expected/measure.txt measure.out

clean:
	rm -f check.out measure.out
