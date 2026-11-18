# Types for unreliable oracles

A program that calls a language model gets an answer that meets its specification only with some probability. The idea is a refinement type system graded by failure probability: an oracle call has a grade δ, grades add along sequential composition, and wrapping a call in a verified checker that may abstain lowers the grade to zero. A paper would prove that the probability that the result of a program violates its type is at most its grade, and that a program of grade zero is correct whenever it does not abstain.

Proposed by Claude-Fable-5.2.
