# Finite transducers for the zero-leakage partition reduction

This volume supplies word and machine obligations for Theorem 4.3 of
[PREDICTIVE_THERMODYNAMIC_SUFFICIENCY.md](https://github.com/the-omega-institute/trureturing/blob/488e3fce13cd3f77e9051ae316dadc0da7f7a4fc/docs/develop/theory/PREDICTIVE_THERMODYNAMIC_SUFFICIENCY.md).
The standing finite-dimensional, support and natural-logarithm conventions are
its Sections 1.2 and 3.1-3.4. The current main-volume presentation is Section 6.4
of SYMPLECTIC_PREDICTIVE_COMPLETION.md.

## 1. Original physical reduction and finite response processing

**theorem 1.1 (Full original partition reduction).** For every explicit universe
of n Boolean variables and every list F of m clauses of length at most three,
the raw violation projectors give the same Hamiltonians
$$
H_F=(n+1)\sum_{j=1}^m\Pi_j,\qquad
H=|1\rangle\langle1|\otimes I+I\otimes H_F,\qquad
\beta=\log2.
$$
The projectors are Hermitian, diagonal, pairwise commuting and supported on at
most three variables, including empty, repeated and tautological clauses.
The full complex matrix exponential and trace satisfy
$$
\#\mathrm{SAT}(F)=\left\lfloor\frac23\operatorname{Tr}e^{-\beta H}\right\rfloor.
$$
A single exact query with a succinct local-term descriptor and ordinary reduced
positive binary rational response suffices, using fixed finite pre- and
post-machines with polynomial running time. The independent standard count is
over the appearing binary variable names. Dense renaming gives the explicit
universe; in the reverse correspondence a tautology for each declared variable
preserves unused variables. Those tautologies do not enter the physical clauses.
Malformed source words use the zero-variable one-empty-clause Hamiltonian,
whose partition is 3/4 and whose recovered count is zero. The visible algebra
has zero leakage and exact prediction for every joint state and time. The same
centered local Hamiltonians give product Gibbs normalization and zero
support-aware recovery defect for every visible state, including singular
states. The zero-variable hidden singleton is treated directly. No efficient
Gibbs preparation, fixed geometry, bounded interaction strength or approximate
hardness is asserted.

**theorem 1.2 (Ordinary dyadic response transducer).** There is a fixed finite
four-stack machine with alphabet {0,1,/}, eleven labels and twenty-four internal
states. On a positive canonical numerator word for p and denominator word
1 followed by e zeros, if 3 divides p and either e=0 or p is odd, it clears the
input and all work stacks, resets its finite state and emits canonical binary
digits for
$$
\begin{cases}
2(p/3),&e=0,\\
\lfloor (p/3)/2^{e-1}\rfloor,&e>0.
\end{cases}
$$
Its real transition count is bounded by a fixed linear polynomial in the whole
ordinary response length. It reads the separator and denominator; no annotated
shift, cut or exponent is supplied. The division state is one of 0,1,2, each
denominator shift is an actual stack mark, and the output zero is one symbol.
Malformed or unsuitable words emit zero after clearing all work stacks.

**theorem 1.3 (Total raw clause codec).** Source mode accepts exactly words
$$
1^n0\,(01\,(11\,b\,1^i0)^{\leq3}\,10)^m\,00,
$$
with each literal index i strictly below n. Physical mode additionally has
prefix 11, the fixed beta and visible tokens 00 and 01, and coefficient
1^(n+1)0 immediately after every clause tag. For every Boolean word, each
mode is a total option-valued decoder. It returns exactly universe n and raw
formula F if and only if the word is their complete encoding and every clause
has at most three literals. No external decoding witness is supplied. The
accepted encoding is unique, including n=0, empty formulas and clauses,
repeated and tautological literals, and unused declared variables. Physical
coefficients and the complete trailing delimiter are checked by the decoder.

**theorem 1.4 (Machine error entry cleanup).** For every finite control state
and arbitrary Boolean contents of input, header, scratch and partial-query
stacks, the fixed pre-machine starting at badInput with empty output reaches
the exact haltList configuration for the valid zero-variable one-empty-clause
dummy query. It resets the finite control and empties all four starting stacks.
The actual step count is bounded by the sum of their lengths plus five. This
error-entry theorem does not assume that the stacks contain unary marks. The
complete parser-to-error-entry bound for every malformed source word is a
separate obligation.

## Append Anchor

## 2. Exact clause preprocessing on all words

Fix the source and physical word conventions of Theorem 1.3 and the same
five-stack pre-machine used in Theorem 1.4. Its alphabets are Boolean, its
nineteen labels and thirty-six control states are fixed independently of the
input, and its initial and terminal configurations have empty work stacks and
reset control. Write $s(F)$ and $q(F)$ for the complete source and physical
encodings of a raw formula $F$, respectively. Let $P$ be the fixed program's
output-push bound, obtained by summing the statement push bounds over its
finite labels, as in `programPushBound`.

**theorem 2.1 (Valid source execution and exact output length).** For every
$n\in\mathbb N$ and every raw formula $F$ over $n$ declared variables, if each
clause has length at most three, the fixed pre-machine started on $s(F)$ reaches
the exact clean terminal configuration with output $q(F)$ in at most

$$
3(|s(F)|+3)^2+7
$$

actual transitions. The output length is exactly

$$
|q(F)|=|s(F)|+6+|F|(n+2).
$$

The declared universe includes unused variables. Empty formulas, empty clauses,
repeated literals and clauses, tautologies and $n=0$ remain allowed.

**theorem 2.2 (Total raw-input clock and output growth).** For every Boolean
word $w$, without any syntax premise, there is a word $o$ such that the same
fixed machine reaches its exact clean terminal configuration with output $o$
within $b(|w|)$ actual transitions, where

$$
b(L)=(4L+20)L+13.
$$

Its output satisfies $|o|\le b(|w|)P$. This clock statement does not identify
the output or infer acceptance from it.

**theorem 2.3 (All-input output refinement and actual rejection prefix).** Let
$D_s(w)$ be the total source decoder. Define $F_w$ to be its decoded universe
and raw formula when decoding succeeds, and to be the zero-variable formula
with one empty clause when decoding fails. Let $Q_w=q(F_w)$ in the successful
case and let $Q_w$ be the fixed dummy query in the failed case. For every raw
Boolean word $w$, the fixed pre-machine reaches the exact clean terminal
configuration with output $Q_w$ within $b(|w|)$ transitions. The physical decoder
returns exactly $F_w$ on $Q_w$, the output is the complete physical encoding of
$F_w$, all its clauses have length at most three, and
$|Q_w|\le b(|w|)P$.

If $D_s(w)$ fails, its actual run has a prefix of at most $b(|w|)$ transitions
reaching `badInput` with empty output and some concrete input, header, scratch
and partial-query stack contents. Theorem 1.4 then applies to that configuration.
A valid source encoding for the zero-variable formula with one empty clause
also emits the same dummy query: acceptance and rejection are distinguished by
the source decoder and the actual error prefix, rather than by output equality.

## Append Anchor 2
