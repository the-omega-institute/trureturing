---
bibkey: johnsonpaparella2025perron
authors: Charles R. Johnson; Pietro Paparella
year: 2025
title: Perron similarities and the nonnegative inverse eigenvalue problem
doi: 10.1090/tran/9596
url: https://arxiv.org/abs/2409.07682v4
claim: "Question 9.1: If K is a polyhedral cone (polytope) that is closed with respect to the Hadamard product, is there an invertible matrix S such that K = 𝒞(S) (K = 𝒫(S))?"
strata_touched:
  - D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation
license: citation-only
triage: anchor
---

# Perron similarities and the nonnegative inverse eigenvalue problem

## Verified locator

DOI: 10.1090/tran/9596

Source: https://arxiv.org/abs/2409.07682v4

Transactions of the American Mathematical Society 378 (2025), 8361–8389.
Page numbers below refer to arXiv v4.

## Source statements

Page 27, Question 9.1: “If K is a polyhedral cone (polytope) that is closed
with respect to the Hadamard product, is there an invertible matrix S such
that K = 𝒞(S) (K = 𝒫(S))?”

Page 10, Definition 4.1: “If S ∈ GLₙ(ℂ), then:”

- “𝒞(S) := {x ∈ ℂⁿ | Mₓ := SDₓS⁻¹ ≥ 0} is called the (Perron) spectracone of S;”
- “𝒫(S) := {x ∈ 𝒞(S) | Mₓe = e} is called the (Perron) spectratope of S;”

Page 5, Section 2.3: “If a ∈ ℂⁿ, a ≠ 0, and b ∈ ℝ, then”

$$\mathsf H(a,b):=\{x\in\mathbb C^n\mid\Re\langle a,x\rangle\ge b\}
=\{x\in\mathbb C^n\mid\Re\langle x,a\rangle\ge b\}$$

“is a closed half-space determined by the hyperplane
{x ∈ ℂⁿ | Re(⟨x, a⟩) = b}.”

“Any set of the form”

$$\bigcap_{k=1}^m\mathsf H(a_k,b_k)
=\bigcap_{k=1}^m\{x\in\mathbb C^n\mid\Re\langle a_k,x\rangle\ge b_k\}$$

“is called a polyhedron and a bounded polyhedron is called a polytope.
Any set of the form”

$$\bigcap_{k=1}^m\mathsf H(a_k)
=\{x\in\mathbb C^n\mid\Re\langle a_k,x\rangle\ge0\}$$

“is called a polyhedral cone.” The finite intersection quantifies every k;
the right-hand set in the last printed expression has a free k.

## Mathematical scope

The Lean proposition asks both converses in every positive coordinate size n.
Vectors use `Fin n → ℂ`, and an invertible diagonalizer has exactly that size.
Half-spaces are real half-spaces on complex Euclidean space. Complex
nonnegativity requires zero imaginary part as well as nonnegative real part.
The all-ones vector is the source's e, and vector multiplication is coordinatewise.

The refutation uses the explicit m = 10 cone in three coordinates. Fourteen
real inequalities describe its real part; six more inequalities impose the three
reality equations. Ten boundary midpoints require distinct active nonzero
linear forms, whereas a three-by-three diagonalizer provides only nine entry
forms. The proof retains the reality conditions for complex diagonalizers.
The unbounded family and the separate polytope converse are not Lean theorems here.

The experiment is in `the-omega-institute/trureturing-experiments`, commit
`4fabe46e24f16239d57cdca75bbedf6aa388ede1`, at
`docs/reports/hadamard-polyhedra/check.py`, SHA-256
`2a1eabfa56e35bd079005d56f593f66e170b2f3ff01210e0b6066011991013d8`.
Its recorded command is `/tmp/op-jp2025/venv/bin/python docs/reports/hadamard-polyhedra/check.py`;
the preregistration records exit 0 and `ALL_CHECKS_OK`. The finite checks and
symbolic common-realization calculation are computational evidence.
Literature-search completeness and comparison with the full journal text are
ASSUMED-UNVERIFIED; the source question here is arXiv v4, as in issue #22419.
