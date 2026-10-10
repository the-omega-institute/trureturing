---
bibkey: bertsekas2015terminaldp
authors: Dimitri P. Bertsekas
year: 2015
title: Dynamic Programming and Stochastic Control, Lecture 10
url: https://ocw.mit.edu/courses/6-231-dynamic-programming-and-stochastic-control-fall-2015/resources/mit6_231f15_lec10/
claim: "Infinite-horizon Bellman problems require a specified cost and termination or discount contract; the finite stochastic shortest-path theorem in Lecture 10 assumes all-policy termination."
strata_touched: []
license: citation-only
triage: anchor
---

# Terminal and discounted Bellman contracts

The [primary MIT lecture](https://ocw.mit.edu/courses/6-231-dynamic-programming-and-stochastic-control-fall-2015/9994ed9e45244c0180c56d830d3716fe_MIT6_231F15_Lec10.pdf),
slide 2, distinguishes undiscounted stochastic shortest paths with a
termination state from discounted problems. Slide 5 specifies the finite
state space, cost-free terminal state and all-policy termination assumption;
slides 6–7 derive finite policy costs and the corresponding Bellman result.
That theorem does not directly cover a graph on which an arbitrary policy
can cycle forever.

The [five-state terminal-clock application](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md),
Section 16, instead restricts to deterministic finite paths reaching a
designated target, positive finite edge costs and reachability from every
vertex. Removing cycles makes the minimum finite and attained; the
first-edge split gives the Bellman equation. A minimizing policy strictly
decreases the value until reaching the target, although other policies
may cycle. The edge residual and its telescoping sum are intermediate
algebra in that application. No all-policy termination, unrestricted
cyclic fixed-point theorem or physical time interpretation is imported.
