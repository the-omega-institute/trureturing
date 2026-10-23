---
bibkey: hiaimosonyihayashi2009groupsymmetry
authors: Fumio Hiai and Milan Mosonyi and Masahito Hayashi
year: 2009
title: Quantum hypothesis testing with group symmetry
doi: 10.1063/1.3234186
url: https://arxiv.org/abs/0904.0704v2
claim: Section 7 asks whether the asymptotic logarithmic overlap is differentiable throughout (0,1) for group-invariant state discrimination.
strata_touched:
  - D5/S3/Quantum/Information/GroupInvariantPsi/Defs
  - D5/S3/Quantum/Information/GroupInvariantPsi/Mixture
  - D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich
  - D5/S3/Quantum/Information/GroupInvariantPsi/Result
license: "not verified; bibliographic attribution and a short attributed quotation, no source proof code copied"
triage: anchor
---

# Quantum hypothesis testing with group symmetry

## Verified locator

DOI: 10.1063/1.3234186

https://arxiv.org/abs/0904.0704v2

F. Hiai, M. Mosonyi and M. Hayashi, *Quantum hypothesis testing with group
symmetry*, J. Math. Phys. 50 (2009) 103304. Section 7 gives the main
open question about differentiability. Equation (2.1) defines the
conditional expectation as the Haar average of tensor conjugates;
equation (3.1) defines the normalized asymptotic logarithmic trace overlap.

## Source objects and formal interpretation

For states on a finite-dimensional complex Hilbert space and a unitary
representation of a compact group, the tensor states are averaged under
the tensor representation. The finite overlap is the logarithm of the trace
of their spectral powers with exponents s and 1-s. Its normalized limit
is denoted by psi. The source proves bounds without assuming
differentiability and asks whether psi is differentiable on (0,1).

`Defs` retains the source objects for finite groups, whose normalized Haar
measure is uniform. It restricts to positive definite trace-one matrices
and makes convergence an explicit premise of the differentiability claim.
A finite-group example in this faithful domain is sufficient to refute the
compact-group assertion. Tensor coordinates are functions from Fin n to
Fin d, and matrix powers use the continuous functional calculus.

## Mathematical consequence

`Mixture` identifies diagonal permutation twirls with classical orbit
mixtures. `Sandwich.psi_eq_max` proves convergence and identifies the
limit with the logarithm of the largest relative orbit overlap for strictly
positive diagonal inputs. `Result.result` refutes the differentiability
claim using p=(16,9,4,1)/30, q=(4,1,9,16)/30 and the involution (12)(34).
The exact left and right slopes are respectively -(2/7)log(4/3) and
(2/7)log(4/3).

Mosonyi–Szilágyi–Weiner, arXiv:2011.04645, Remark IV.9 addresses the
separate conjecture psi=psi° with an invariant alternative hypothesis.
That statement is distinct from the differentiability assertion treated here.
