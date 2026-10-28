# Whole worlds and literal acquisition histories

## Abstract

Whole worlds and literal acquisition histories

For any declared natural maximum degree d, Coeff d is the real vector space indexed by Fin(d+1). The polynomial gain d beta is Polynomial.ofFn(d+1,beta), with ascending ordinary coefficients. World d contains a strictly entrywise positive real 2 by 2 source of matrix rank one and trace one, a nonzero coefficient vector, and an arbitrary real drift. No individual coefficient, sampled value, root multiplicity, sign, or actual degree is constrained. Statements about the adaptive threshold additionally require d>=1.

Every nonzero real polynomial g of natural degree at most d has the unique vector of its first d+1 coefficients. Polynomial.toFn_comp_ofFn_eq_id and Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt give the exact two inverse laws; injective_ofFn identifies the nonzero predicates. Thus this coefficient domain covers exactly the original whole-polynomial domain, preserving the source and drift.

The sourceChart(x,r) is the matrix [1,r;x,xr] divided by 1+xr. For x,r>0 it is strictly positive, rank one, and trace one. Every legal original source is exactly one such matrix, with recovered coordinates x=P10/P00 and r=P01/P00. The denominator is strictly positive. No auxiliary source restriction is introduced.

**Theorem 1.1 (Legality of every positive chart point).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.source_chart_legal`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.source_chart_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x,r in the reals, 0<x and 0<r imply LegalSource(sourceChart x r). This means every entry is positive, its matrix rank is one, and its trace is one.

**Theorem 1.2 (Every original source is represented).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.source_chart_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.source_chart_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 2 by 2 matrix P satisfying LegalSource P there exist positive real x,r with P=sourceChart x r, x=P10/P00, and r=P01/P00. The rank-one hypothesis gives determinant zero; trace one reconstructs the positive denominator.

evaluation(d,n,t) has entries t(i) to the power k for i in Fin n and k in Fin(d+1), with the usual convention that a zeroth power is one. evaluate is its real linear multiplication map on ordinary coefficients. It is exactly evaluation of gain d beta at the specified nodes.

The nodes are explicit. clocks n i is the real cast of the original natural index i. Interpolation at arbitrary distinct nodes is an algebraic interface; literal acquisition continues to use every consecutive original clock. The zero-node case and the empty value vector are included.

**Theorem 1.3 (Ordinary polynomial and matrix evaluations agree).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.evaluation_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.evaluation_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n, node function t:Fin n to the reals, ordinary coefficient vector beta:Coeff d, and index i:Fin n, evaluate(d,n,t)(beta)(i) equals gain(d,beta) evaluated at t(i). No injectivity of t or nonzero condition on beta is needed for this exact equality.

**Theorem 1.4 (Enough distinct clocks determine all coefficients).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.evaluation_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.evaluation_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n and t:Fin n to the reals, injectivity of t and d+1<=n imply injectivity of evaluate d n t. Two coefficient vectors with these evaluations equal represent polynomials of degree less than d+1 agreeing at n distinct nodes, so they coincide.

**Theorem 1.5 (Every short vector of prescribed values occurs).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.evaluation_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.evaluation_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n and injective t:Fin n to the reals, n<=d+1 implies surjectivity of evaluate d n t. Lagrange interpolation supplies a polynomial of degree less than n; its first d+1 coefficients give the witness. For n=0 the unique empty vector is attained by zero.

**Theorem 1.6 (Coefficient-and-drift history extension is onto).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.pureJ_history_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.pureJ_history_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n with n<=d+1, the map from Coeff d times the reals to real Fin n vectors, sending (beta,delta) to the vector gain(d,beta)(clocks n i)+delta, is surjective. The witness may take drift zero. This is the extension to the full coefficient space; it does not claim nonzero-gain fiber completion.

A chronological word is a list of Booleans: false is M=[0,1;1,1], and true is J=[0,1;1,0]. acquisition is the real cast of the integral chronological word. Its empty word is the identity. Appending an atom multiplies the cumulative matrix on the left by exactly that atom. This connects the real sensor directly to the integral word laws.

readAt W w i is gain(d,W.coeff)(i) times trace(acquisition(take i w) W.source), plus W.drift. readings W w restricts this expression to Fin(length(w)+1). Thus the identity read at clock zero is present, and every atom has exactly one immediately following read. The finite history contains the original clocks 0 through length(w). No reset, copied source, skipped read, extra sensor or clock renumbering is part of the protocol.

A Readout d w is a fixed real matrix with d+1 rows and length(w)+1 columns. Collinear allows an arbitrary real scalar, including zero. Succeeds requires a nonzero real scalar, of either sign, multiplying the whole coefficient vector. Zero output never counts as success.

A Protocol fixes a countable set of matrices for each word before observations. Its decide function takes the entire word and its entire real history and either chooses one next M or J, or stops with a member of that word's fixed palette. Empty, finite and countably infinite palettes are permitted. No continuity, measurability, computability or finite response alphabet is assumed.

Reaches is an inductive actual execution predicate. It starts with the initial read and extends only when decide selects the next atom from the already acquired history. Terminates also requires the stop decision to select its stated palette member. UniformlySuccessful P N requires on every original World d an actual terminating execution with at most N total reads whose selected matrix succeeds. Gain-only correctness is the nonzero scalar condition; complete-target recovery is a separate task.

**Theorem 1.7 (Real and integral chronological acquisition agree).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.acquisition_append`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.acquisition_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word w and Boolean a, acquisition(w++[a])=action(a) acquisition(w). This uses the chronological append conjunct of raw_word_signed_bound under the real ring homomorphism.

**Theorem 1.8 (Literal repeated atoms are matrix powers).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.acquisition_pure`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.acquisition_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean a and natural n, acquisition of n repeated copies of a equals action(a) to the power n. The identity at n=0 and chronological append at n+1 give this native power interface for both M and J.

**Theorem 1.9 (Actual prefixes transfer through arbitrary decisions).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.identical_prefix_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.identical_prefix_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, protocol P, worlds W and Wprime, and word w, if Reaches P W w and readings W w=readings Wprime w, then Reaches P Wprime w and P.decide w gives the same decision on these two histories. The proof restricts the final equal history to each prior word and inducts through the actual execution.

**Theorem 1.10 (The same first M is actually executed).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.identical_prefix_firstM`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.identical_prefix_firstM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d,P,W,Wprime and natural n, suppose P actually reaches the word of n copies of J on W, the two worlds have identical readings on that word, and its next decision on W is M. Then P actually reaches J repeated n followed by M on Wprime. The transferred M is at original clock n+1. This includes n=0 and imposes no equality of subsequent histories or terminal words.

**Theorem 1.11 (A terminal word extends every acquired prefix).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.terminal_extends_reached`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.terminal_extends_reached` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d, protocol P, world W, words p,w and member C of the fixed palette at w, Reaches P W p and Terminates P W w C imply that p is a prefix of w. Reached words of the same length are equal, by induction through their actual deterministic decisions. Every initial part of a reached word is reached. A terminal word cannot be shorter than another reached word, because its stop decision would then equal an action decision. Thus a forced M remains present in the terminal word supplied by a uniform read bound.

chartWorld takes any positive chart coordinates x,r, any nonzero whole coefficient vector beta, and any real drift delta to a World d. source_chart_exact supplies the reverse source representation for every original world.

identicalRow(theta)=[1-theta,theta;1-theta,theta] is legal for 0<theta<1. rowWorld combines this source with any nonzero ordinary coefficient vector and any drift. Its positive source chart is x=1, r=theta/(1-theta). Left multiplication by J fixes the matrix, hence every pure-J cumulative matrix fixes it as well.

**Theorem 1.12 (Pure J factors on every legal source chart).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.source_chart_pureJ`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.source_chart_pureJ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real x,r and natural n, trace(acquisition(J repeated n) sourceChart(x,r)) equals one when n mod 2 is zero, and equals (x+r)/(1+xr) otherwise. Both factors are strictly positive on the positive chart. The equality uses the literal native power interface and J squared equal to the identity.

**Theorem 1.13 (Every identical-row source in the open interval is legal).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.identical_row_legal`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.identical_row_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta with 0<theta<1, identicalRow theta is strictly entrywise positive, has matrix rank one, and has trace one.

**Theorem 1.14 (All pure-J reads use the original whole gain).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.identical_row_readings`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.identical_row_readings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d, theta with 0<theta<1, nonzero beta:Coeff d, real drift delta and natural n, readings(rowWorld(d,theta,beta,delta),J repeated n) is the vector gain(d,beta)(i)+delta at its original Fin(length(J repeated n)+1) clocks. This includes the initial read and the empty action word. No sampled-zero, sign or lower-degree case is excluded.

**Theorem 1.15 (Every acquired initial part is actually reached).**

Lean statement: `D5/S3/Observer/Linear/GainRayHistory.reaches_take`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayHistory.reaches_take` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prefix of a reached word, up to its literal action length, is reached on the same actual world.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.acquisition_append`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.acquisition_pure`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.evaluation_injective`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.evaluation_polynomial`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.evaluation_surjective`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.identical_prefix_firstM`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.identical_prefix_transfer`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.identical_row_legal`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.identical_row_readings`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.pureJ_history_surjective`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.reaches_take`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.source_chart_exact`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.source_chart_legal`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.source_chart_pureJ`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.terminal_extends_reached`
- Dependency: [D5/S3/Arith/FibonacciAtomic/SelfCalibratingRawWords](../../Arith/FibonacciAtomic/SelfCalibratingRawWords.md)
