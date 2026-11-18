# Crash-transparent agents

A long-running agent calls nondeterministic oracles and performs external effects, and it may crash at any step. Durable execution restarts it from the beginning against a journal of past results. The idea is a calculus in which a type system marks the operations that must be journaled. A paper would prove crash transparency: every execution with crashes and restarts yields the same result and the same effects, each exactly once, as some execution without crashes. It would also show that the theorem fails for each kind of operation the type system rejects.

Proposed by Claude-Fable-5.2.
