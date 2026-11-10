# Prime-Support Detection of Finite Cyclic Projectivity

## Abstract

Prime-support subgroups detect projectivity for every finite cyclic group over arbitrary commutative coefficients.

**Theorem 1.1 (The full finite cyclic prime-support detector).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/CyclicSubgroupProjectivity.projective_iff_projective_prime_support_subgroup`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/CyclicSubgroupProjectivity.projective_iff_projective_prime_support_subgroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact public telescope: universe uR uG uV; {R : Type uR} {G : Type uG} {V : Type uV} [CommRing R] [Group G] [Fintype G] [IsCyclic G] [AddCommGroup V] [Module R V] (rho : Representation R G V) (H : Subgroup G) (hsupport : forall p : Nat, p.Prime -> p divides Nat.card G -> p divides Nat.card H). The conclusion is Module.Projective R[G] rho.asModule iff Module.Projective R[H] Representation.asModule (rho.comp H.subtype : Representation R H V). The ring, group and module universes are independent. No prime-power order, field, characteristic, nilpotence, invertible cardinality, finite generation, finite presentation, Noetherianity or nontriviality premise is present. Zero rings, zero modules and trivial groups remain in scope.

Write q=H.index and r=Nat.card H. Finiteness and the group identity give r>0 by Nat.card_pos. The finite quotient gives q>0 by H.index_ne_zero_of_finite. H.index_mul_card gives q*r=Nat.card G, and H.index_dvd_card gives q divides Nat.card G. Thus hsupport supplies every prime divisor of q as a divisor of r. These positivity, index and support facts are proved in the endpoint, not added to its telescope.

Choose an actual generator g by IsCyclic.exists_generator and obtain orderOf g=Nat.card G by orderOf_eq_card_of_forall_mem_zpowers. The private index_generator_subgroup proves the cardinality recognition: q divides orderOf g, and orderOf_pow_of_dvd computes orderOf(g^q)=Nat.card G/q=(q*r)/q=r. Nat.card_zpowers and IsCyclic.subgroup_eq_iff_card_eq identify zpowers(g^q) with the supplied H. This includes q=1 and r=1; there is no nontrivial-group branch or implicit prime-power restriction.

generator_powers_bijective proves that i maps to g^i is bijective from Fin(Nat.card G) to G. It uses pow_injOn_Iio_orderOf with strict bounds from the actual generator order and obtains bounded exponents from IsCyclic.image_range_card. sum_generator_powers uses Fintype.sum_bijective and Fin.sum_univ_eq_sum_range. Both G and the subgroup H are enumerated exactly once.

For A=Module.End R V, conjugation rho g is a real ring automorphism, constructed from rho.asGroupHom g via LinearMap.GeneralLinearGroup.toLinearEquiv and LinearEquiv.conjRingEquiv. conjugation_apply proves its formula (rho g).comp(t.comp(rho(g inverse))) by map_inv on the actual unit-valued representation. conjugation_one, conjugation_mul and conjugation_pow prove that conjugation by g^i is the i-th automorphism power. The product inverse is h inverse times g inverse for g*h. Multiplication in A means composition; no arbitrary endomorphism factors are interchanged.

group_trace_eq_norm identifies the literal G-conjugation trace with norm sigma (Nat.card G), with sigma=conjugation rho g. subgroup_trace_eq_norm constructs h : H from g^q, obtains an integer-power representation of every element of H using the recognition equality, and proves h generates H by subtype extensionality. The same bounded enumeration and conjugation_pow then identify the literal restricted trace of rho.comp H.subtype with norm (sigma^q) r. The subgroup identification, trace conversions and action are constructed, not assumed.

The new private prime_support_norm_one proves the generic ring implication: for arbitrary Ring A, any ring automorphism sigma, q,r>0 and every prime divisor of q dividing r, an element with (sigma^q,r)-norm one yields an element with (sigma,q*r)-norm one. Strong induction is on q while generalizing sigma and r. At q=1 reuse the input witness. Otherwise Nat.exists_prime_and_dvd chooses p prime dividing q; write q=p*qprime. Positivity of q forces qprime>0, and p>1 gives qprime<q by lt_mul_of_one_lt_left. The support assumption gives p divides r, so write r=c*p. No characteristic or scalar cancellation is introduced.

Normalize the input norm as the p-step norm for sigma^qprime: (sigma^qprime)^(p*i)=sigma^(q*i). Apply the original CyclicNormOne.exists_norm_one_lift to sigma^qprime with parameters p,r,c, using p>0, r>0 and r=c*p. This gives a witness with (sigma^qprime,p*r)-norm one. Every prime l dividing qprime divides q and hence r, so also divides p*r. The induction hypothesis at qprime and new length p*r now gives the (sigma,qprime*(p*r))-norm-one witness. Normalize qprime*(p*r)=(p*qprime)*r=q*r. Only natural-number multiplication and powers of the same automorphism are rearranged; the original noncommutative ring construction and its multiplication order are reused without duplication. No automorphism-period premise is needed.

For restriction, a full norm-one element t gives the subgroup witness norm sigma q t. The original norm_comm and norm_blocks give norm (sigma^q) r (norm sigma q t)=norm sigma q (norm (sigma^q) r t)=norm sigma (q*r) t=1. These are the existing finite-sum proofs at their CyclicNormOne owner, consumed through the norm, norm_comm and norm_blocks APIs. The converse uses prime_support_norm_one. Neither direction repeats the owner's norm proofs or addresses private declarations through mangled names.

Apply ProjectiveConjugationTrace.projective_iff_projective_and_conjugation_trace_one to rho and to rho.comp H.subtype. Each side retains the same essential Module.Projective R V condition. G-projectivity supplies it and a full trace-one witness; norm descent supplies the restricted witness. H-projectivity supplies coefficient projectivity and a restricted trace-one witness; the new norm induction supplies the full witness. The trace criterion then gives G-projectivity. Identity in End_R(V) is LinearMap.id even for the zero module.

The condition is mathematically sharp UNIFORMLY over coefficient rings: if a prime p divides the group order but not the subgroup order, take the trivial module F_p over R=F_p. Its base module is free and |H| is invertible, so |H| inverse times the identity has H-trace one and the restricted module is R[H]-projective. Conjugation on End_R(F_p)=F_p is trivial, so every G-trace is multiplication by |G|=0. Since the identity is nonzero, the trace criterion rules out R[G]-projectivity. This is an ordinary mathematical explanation of uniform necessity, not a separately formalized counterexample or an additional Lean uniform-iff declaration. Necessity need not hold for each fixed R: over Q every subgroup detects projectivity, since |G| is invertible.

As a direct application, when Nat.card G=p^n for p prime and H has order p, the prime-support hypothesis holds and this detector supplies the former specialized conclusion. The same theorem applies directly without a separate specialized endpoint.

For finite cyclic G, the subgroup of each prime order dividing |G| is unique, so the prime-support condition on H puts every prime-order element of G in H. This places the detector in the finite Moore/Chouinard framework. Eli Aljadeff, Profinite groups, profinite completions and a conjecture of Moore, arXiv:math/0405201, Theorems 2.4 and 2.5 (https://ar5iv.labs.arxiv.org/html/math/0405201), explicitly recalls elementary-abelian projectivity detection over arbitrary unital rings and for arbitrary modules, together with the unit-order Maschke case, and states their finite Moore consequence. The underlying elementary-abelian reference is Aljadeff--Ginosar, Induction from elementary abelian groups, J. Algebra 179 (1996), 599--606. The general elementary-abelian theorem and general Chouinard/Serre theory are not formalized in this module. The proof here gives an explicit cyclic route using the endomorphism ring, the full conjugation-trace criterion and the period-free finite norm construction, without a field, finite-generation, group-order division or cohomological nilpotence premise. The ordinary finite-cyclic proof was supplied by Pro, observed metadata gpt_6 with pro effort, task cbbd2223-6e8f-48bd-9076-3c7fe0a6f854. The norm-lift source context is E. Aljadeff and C. Kassel, Explicit elements of norm one for cyclic groups, https://arxiv.org/abs/math/0012038. No novelty claim is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/CyclicSubgroupProjectivity.projective_iff_projective_prime_support_subgroup`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/CyclicNormOne](CyclicNormOne.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ProjectiveConjugationTrace](ProjectiveConjugationTrace.md)
