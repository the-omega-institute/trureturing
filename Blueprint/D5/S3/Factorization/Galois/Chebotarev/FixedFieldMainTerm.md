# the degree-one part of T carries the main term

## Abstract

the degree-one part of T carries the main term.

**Theorem 1.1 (the degree-one part of T carries the main term).**

Lean statement: `D5/S3/Factorization/Galois/Chebotarev/FixedFieldMainTerm.primeIdealZetaSum_fibre_eq_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/Chebotarev/FixedFieldMainTerm.primeIdealZetaSum_fibre_eq_smul` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Let L/K be finite Galois, σ ∈ Gal(L/K), E = L^⟨σ⟩, and σ_E ∈ Gal(L/E) restrict to σ. Assume Gal(L/E) is abelian and f = ord(σ) = |Gal(L/E)|. For s > 1, the prime-ideal Dirichlet sum over T₁, consisting of E-primes with L/E Frobenius [σ_E], degree one over K, and unramified base prime, equals |G|/(f·|C|) times the sum over S, the unramified K-primes with Frobenius class C = [σ]. The fibre over each 𝔭 ∈ S has exactly |G|/(f·|C|) such primes P (the fibre bijection card_fibre_E_eq_card_fibre_L together with the proven count count_primes_above_with_frobenius_eq_sigma), and N P = N 𝔭 for degree-one P.

## References

- Truth anchor: `D5/S3/Factorization/Galois/Chebotarev/FixedFieldMainTerm.primeIdealZetaSum_fibre_eq_smul`
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/Cyclotomic](Cyclotomic.md)
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/FixedFieldFrobeniusCounting](FixedFieldFrobeniusCounting.md)
