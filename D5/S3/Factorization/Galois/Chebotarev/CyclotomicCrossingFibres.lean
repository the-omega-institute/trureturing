/- GID: D5/S3/Factorization/Galois/Chebotarev/CyclotomicCrossingFibres
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/CyclotomicCrossingFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Admissible cyclotomic crossing yields pairwise-disjoint Frobenius subfibres of equal density. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.Cyclotomic
public import D5.S3.Factorization.Galois.Chebotarev.FixedFieldDensity
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Chebotarev's theorem: abelian case

For an abelian Galois extension `L/K` of number fields and any
`σ ∈ Gal(L/K)`, the Dirichlet density of primes `𝔭` of `𝓞 K` (unramified in
`L`) whose Frobenius equals `σ` is `1 / |Gal(L/K)|`.

The proof reduces to the cyclotomic case by *crossing with cyclotomic
extensions* (Chebotarev's original technique). For `m` coprime to the
discriminant of `L`, the field `L(μ_m)` is Galois over `K` with
`Gal(L(μ_m)/K) ≅ G × H` where `H = Gal(K(μ_m)/K) ⊆ (ℤ/mℤ)^×`. For `τ ∈ H`
with `|G| | ord(τ)`, the subgroup `⟨(σ, τ)⟩` has trivial intersection with
`G × {1}`, so its fixed field `F` satisfies `F(μ_m) = L(μ_m)` — making
`L(μ_m)/F` cyclotomic. The cyclotomic case applied to `L(μ_m)/F` and
`(σ, τ)` gives
`δ_F(primes P with σ_P = (σ, τ)) = 1/(|G| · |H|)`, and the (cyclic)
reduction lifts this through `F/K` to a lower-density bound on the primes
of `K` with Frobenius `σ`. Summing over `τ ∈ H_n = {τ : n | ord(τ)}`,

  δ_inf,K({𝔭 : σ_𝔭 = σ}) ≥ |H_n| / (|G| · |H|).

As `m` varies (chosen via Dirichlet's theorem to satisfy `m ≡ 1 mod n^k` for
large `k`), `|H_n|/|H| → 1`, so `δ_inf ≥ 1/|G|`. Summing over `σ ∈ G` then
forces equality.

## Main results

* `Chebotarev.chebotarev_abelian` — the density of primes
  of `K` unramified in an abelian extension `L/K` with Frobenius equal to
  `σ` is `1/|Gal(L/K)|`.

## References

* Sharifi, *Algebraic Number Theory*, §7.2.2 Step 2 (`docs/algnum.pdf`,
  pp. 143–144).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  paragraph 4 (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open NumberField Filter Topology

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Sub-lemmas for `chebotarev_abelian`

Decomposed per Sharifi 7.2.2 Step 2 (p. 143–144). Source quote
(verbatim, p. 143):

> "Choose m ≥ 1 not dividing the discriminant of L so that H =
> Gal(L(μ_m)/L) is isomorphic to (ℤ/mℤ)^× via the mod m cyclotomic
> character, and Gal(L(μ_m)/K) ≅ G × H. For σ ∈ G and τ ∈ H, let S_σ be
> the set of primes of K unramified in L with Frobenius σ in G, and let
> S_{σ,τ} be the set of primes of K unramified in L(μ_m) with Frobenius
> (σ,τ) ∈ G × H. Then δ_inf(S_σ) = Σ_{τ∈H} δ_inf(S_{σ,τ})."

And (p. 144):
> "Now suppose that |G| divides the order of τ. Then ⟨(σ,τ)⟩ ∩ (G × {1})
> = 1, which implies that L(μ_m) is given by adjoining μ_m to F =
> K(μ_m)^⟨(σ,τ)⟩."
>
> "[…] δ(S_{σ,τ}) exists and equals 1/|G||H|."
>
> "|H_n|/|H| = ∏_{i=1}^r (1 - p_i^{k_i-1}/p_i^{j_i k_i}) ≥ ∏_{i=1}^r
> (1 - 1/p^{(j-1)k_i + 1}) so |H_n|/|H| tends to 1 as j increases."

Five sub-lemmas (mirror Sharifi's structure):
-/

/-! ### Cyclotomic-crossing core `exists_cyclotomicCrossing_fibres` (Sharifi 7.2.2 Step 2)

Sharifi 7.2.2 Step 2 cyclotomic-crossing core (p. 144). For `m ≥ 1` and `σ ∈ G`,
there is a family of prime sets `S_{σ,τ}` of `K` indexed by `τ ∈ H_n(m) =
{τ : (ℤ/mℤ)ˣ // |G| ∣ ord τ}`, pairwise disjoint, each contained in the Frobenius
fibre `S_σ`, and each of Dirichlet density exactly `1/(|G|·|H(m)|)` (with
`H(m) = (ℤ/mℤ)ˣ`).
This is the substantive geometric content of the crossing: introduce the compositum
`M = L(μ_m)` (`Gal(M/K) ≅ G × H` via the mod-`m` cyclotomic character, valid since `m`
coprime to `disc L` makes `L` and `K(μ_m)` linearly disjoint over `K`). For each such
`τ`, the subgroup `⟨(σ,τ)⟩` meets `G × {1}` trivially
(`cyclic_subgroup_meets_G_times_one_trivially`), so `M = F(μ_m)` with
`F = K(μ_m)^{⟨(σ,τ)⟩}`, making `M/F` cyclotomic; the cyclotomic asymptotic ratio at
`M/F` and `(σ,τ)`, together with the cyclic reduction through `F/K`, gives a set
`S_{σ,τ}` of primes of `K` with `Gal(M/K)`-Frobenius `(σ,τ)` of density
`1/(|G|·|H|)`. Such primes have `Gal(L/K)`-Frobenius the `G`-projection `σ`, so
`S_{σ,τ} ⊆ S_σ`; distinct `τ` give disjoint sets.

This existence statement packages the compositum infrastructure (`Gal(L(μ_m)/K) ≅ G × H`
and the density transfer `F/K`); the `liminf` lower bound
`liminf_density_S_sigma_ge_card_H_n_div_GH` is assembled around it.

**Hypotheses.** The crossing is only valid at *admissible* `m`:
* `hcop : ((NumberField.discr L).natAbs).Coprime m` — coprimality of `m` to the
  discriminant of `L` is exactly what makes `L` and `K(μ_m)` linearly disjoint over `K`
  (`[K(μ_m):K] = φ(m)` and `Gal(L(μ_m)/K) ≅ G × (ZMod m)ˣ`): the intersection
  `L ∩ K(μ_m)` is unramified everywhere over `K` — the `K`-side via
  `NumberField.discr_dvd_discr` (a prime ramifying in `K(μ_m)` divides `m`, hence not
  `disc L`) and the `L`-side dually — so it is `K` itself (Minkowski).
* `hm4 : m % 4 ≠ 2` — used by the cyclotomic Frobenius-fibre asymptotic to rule out
  the degenerate `m ≡ 2 mod 4` cyclotomic field.
As stated with `∀ m ≥ 1` the conclusion is false/unprovable at degenerate `m`; the
consumer `liminf_ratio_ge_inv_card_G` chooses `m` prime with `m ≡ 1 mod 4·|G|^k`, which
secures both hypotheses (`m % 4 = 1`; a prime exceeding `|disc L|` is coprime to it). -/
/-! #### Internal decomposition of `exists_cyclotomicCrossing_fibres`

The crossing's geometric content is isolated in the *tagged-family* master leaf
`exists_crossing_family_tagged` below: it produces the per-`τ` fibre sets `S_{σ,τ}` of `K`
*together with a single global tag* `t : Ideal (𝓞 K) → (ℤ/mℤ)ˣ` recording the
`H`-component of each prime's `Gal(M/K) = G × H`-Frobenius. The tag makes distinct-`τ` fibres
disjoint (a prime has one well-defined `M`-Frobenius), so `exists_cyclotomicCrossing_fibres`
reduces to that master leaf by a generic *distinct-tags ⟹ pairwise-disjoint* argument
by injectivity of the tag.

The master leaf is in turn intended to be discharged from the following five TRUE
infrastructure leaves (Sharifi 7.2.2 Step 2, p. 144), each independently attackable and
stated against the compositum `M = L(μ_m)` (carrier `CyclotomicField m L` with its
`K`-algebra/scalar-tower structure). They are pinned here as the decomposition targets:

* `cyclotomicField_finrank_eq` (C2a) — `[K(μ_m):K] = φ(m)` from `hcop` (the deep
  ramification/Minkowski input: a prime ramifying in `K(μ_m)` divides `m`, hence is coprime
  to `disc L`, so `K ∩ L = K` and `Gal(K(μ_m)/K) ≅ (ℤ/mℤ)ˣ` has full order `φ(m)`).
* `compositum_charProd_bijective` / `autToPow_L_bijective` (C1) — the `G × H` splitting
  `Gal(M/K) ≅ Gal(L/K) × (ℤ/mℤ)ˣ` via the restriction-pair and the mod-`m` cyclotomic
  character (uses the linear-disjointness degree count C2a / `hcop`).
* Fixed-field cyclotomicity (C3) — for any `g ∈ Gal(M/K)` the fixed field
  `F = M^⟨g⟩` has `M/F` cyclotomic; applied at `g = (σ,τ)`, where the trivial meet
  `⟨(σ,τ)⟩ ∩ (G × {1}) = 1` (`cyclic_subgroup_meets_G_times_one_trivially`, needs
  `|G| ∣ ord τ`) gives `M = F(μ_m)`. The Lean encoding of
  `G × {1} = Gal(M/K(μ_m))` is `(IntermediateField.adjoin K {b | b^m=1}).fixingSubgroup`, NOT
  `ker(restrictNormalHom L)` (which is `{1} × H = Gal(M/L)`).
* Frobenius restriction — a prime with `Gal(M/K)`-Frobenius `(σ,τ)` has
  `Gal(L/K)`-Frobenius the projection `σ` (restriction-compatibility of `frobeniusClass`,
  using the `M/L/K`-tower Frobenius restriction argument below).
* `density_lift_through_fixedField` transfers the cyclotomic density over `M/F` to the
  Frobenius fibre over `K`. `hm4` supplies the cyclotomic hypothesis and `hcop` supplies
  the degree count. -/

/-! #### Infrastructure leaves for `exists_crossing_family_tagged` (C1–C5)

The five TRUE, independently-attackable leaves the master leaf composes (Sharifi 7.2.2 Step 2,
p. 144), stated against the compositum `M = L(μ_m)`. Recommended carrier: `CyclotomicField m L`
(it carries `[IsCyclotomicExtension {m} L M]`, `[NumberField M]`, `[FiniteDimensional L M]`
automatically; its `K`-algebra/scalar-tower structure comes from `RingHom.comp` /
`IsScalarTower.of_algebraMap_eq`). The leaves below abstract `M` as a hypothesis with the
relevant instance binders so they do not depend on that carrier choice. -/

/-- **C2a — cyclotomic degree over the base** (the deep ramification/Minkowski leaf). Source
(Sharifi p. 144): "Choose `m` not dividing the discriminant of `L` so that
`H = Gal(L(μ_m)/L) ≅ (ℤ/mℤ)ˣ` … and `Gal(L(μ_m)/K) ≅ G × H`." The full order `φ(m)`
of `H = (ℤ/mℤ)ˣ` is exactly `[K(μ_m):K] = φ(m)`, equivalently irreducibility of the `m`-th
cyclotomic polynomial over `K`; this holds because `m` is coprime to `disc L` (`hcop`): a
prime ramifying in `K(μ_m)` divides `m`, hence does not divide `disc L`, so `K ∩ L` is
unramified everywhere over `K` and equals `K` (Minkowski / `NumberField.discr_dvd_discr`),
giving linear disjointness of `L` and `K(μ_m)`. -/
private theorem cyclotomicField_finrank_eq
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    Module.finrank K M = m.totient := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set K₁ : IntermediateField ℚ M := IntermediateField.adjoin ℚ {ζ} with hK₁def
  set K₂ : IntermediateField ℚ M := (IsScalarTower.toAlgHom ℚ K M).fieldRange with hK₂def
  haveI hK₁cyc : IsCyclotomicExtension {m} ℚ K₁ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  haveI : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois (S := {m}) (K := ℚ) (L := K₁)
  have hfinK₁ : Module.finrank ℚ K₁ = m.totient :=
    IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    have hζalg : IsAlgebraic ℚ ζ := Algebra.IsAlgebraic.isAlgebraic ζ
    have hsubalg : (IsScalarTower.toAlgHom ℚ K M).range ⊔ Algebra.adjoin ℚ {ζ}
        = (⊤ : Subalgebra ℚ M) := by
      have htop : (Algebra.adjoin K {ζ} : Subalgebra K M) = ⊤ :=
        IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ
      rw [← Algebra.Subalgebra.restrictScalars_adjoin (R := ℚ) (S := K) (s := {ζ}), htop,
        Subalgebra.restrictScalars_top]
    apply IntermediateField.toSubalgebra_injective
    rw [hK₁def, hK₂def, IntermediateField.sup_toSubalgebra_of_isAlgebraic_left,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg,
      AlgHom.fieldRange_toSubalgebra, IntermediateField.top_toSubalgebra, sup_comm]
    exact hsubalg
  let eK₂ : K ≃+* K₂ := ((IsScalarTower.toAlgHom ℚ K M : K →+* M)).rangeRestrictFieldEquiv
  have hdiscrK₂ : NumberField.discr K₂ = NumberField.discr K :=
    (NumberField.discr_eq_discr_of_ringEquiv (f := eK₂)).symm
  have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
    rw [hdiscrK₂, Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hpdvd
    obtain ⟨hpa, hpb⟩ := hpdvd
    have hpm : p ∣ m := (show ∀ (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ K₁] {p : ℕ} (hp : p.Prime) (hpd : p ∣ (NumberField.discr K₁).natAbs), (p ∣ m) from by
      intro m root119Instance0 root119Instance1 p hp hpd
      classical
      by_contra hpm
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      refine absurd (Int.ofNat_dvd_left.mpr hpd) ?_
      rw [NumberField.not_dvd_discr_iff_forall_liesOver K₁ (𝓞 K₁) hpprime]
      intro P hPmax hlo
      haveI := hPmax.isPrime
      haveI := hlo
      have hspanbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]; exact hpprime.ne_zero
      have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspanbot P
      rw [← Ideal.ramificationIdx_eq_one_iff]
      exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K₁ P hpm) m hp hpa
    have hpgcd : p ∣ Nat.gcd (NumberField.discr K).natAbs m := Nat.dvd_gcd hpb hpm
    rw [hcop] at hpgcd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpgcd)
  have hld : K₁.LinearDisjoint K₂ :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := M) K₁ K₂ hcoprime
  have hfr : Module.finrank K₂ M = Module.finrank ℚ K₁ :=
    hld.finrank_right_eq_finrank hsup
  have hrelabel : Module.finrank K M = Module.finrank K₂ M := by
    refine Algebra.finrank_eq_of_equiv_equiv eK₂ (RingEquiv.refl M) ?_
    ext x
    change ((eK₂ x : M)) = (IsScalarTower.toAlgHom ℚ K M : K →+* M) x
    rfl
  rw [hrelabel, hfr, hfinK₁]

/-- **Joint-restriction bijectivity** — the analytic heart of C1, exposed with the explicit
primitive root `ζ` so that callers (C1 and the master leaf) can read off the two components.
The map `Φ = (restrictNormalHom L).prod (autToPow K hζ) : Gal(M/K) →* Gal(L/K) × (ℤ/mℤ)ˣ` is
bijective: injective because an automorphism trivial on `L` and fixing `ζ` is trivial on
`M = L(ζ)`; surjective by the degree count `[M:K] = [L:K]·φ(m) = [L:K]·[M:L]`
(`cyclotomicField_finrank_eq` at base `L`, hence `hcop`). -/
private theorem compositum_charProd_bijective
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hcop : ((NumberField.discr L).natAbs).Coprime m) (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  haveI : FiniteDimensional K M := inferInstance
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  set χK : Gal(M/K) →* (ZMod m)ˣ := hζ.autToPow K with hχK
  set Φ : Gal(M/K) →* Gal(L/K) × (ZMod m)ˣ :=
    (AlgEquiv.restrictNormalHom L).prod χK with hΦ
  have hML : Module.finrank L M = m.totient := cyclotomicField_finrank_eq L M m hcop
  have hcardMK : Nat.card Gal(M/K) = Nat.card Gal(L/K) * Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, hML, Nat.card_eq_fintype_card (α := (ZMod m)ˣ),
      ZMod.card_units_eq_totient]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    rw [hΦ, MonoidHom.prod_apply, Prod.mk_eq_one] at hσ
    obtain ⟨hσL, hσζ⟩ := hσ
    have hζfix : σ ζ = ζ := by
      have hspec := hζ.autToPow_spec K σ
      rw [hχK] at hσζ
      rw [hσζ] at hspec
      rw [← hspec, Units.val_one]
      rcases eq_or_lt_of_le (NeZero.one_le (n := m)) with h1 | h1
      · have hm1 : m = 1 := h1.symm
        subst hm1
        have : ζ = 1 := by simpa using hζ.pow_eq_one
        simp [this]
      · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by lia), pow_one]
    have hLfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
      intro x
      have hcomm := σ.restrictNormal_commutes L x
      have hrn : σ.restrictNormal L = (1 : Gal(L/K)) := hσL
      rw [hrn] at hcomm
      simpa using hcomm.symm
    have htop : Algebra.adjoin L {ζ} = (⊤ : Subalgebra L M) :=
      IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ Algebra.adjoin L {ζ} := htop ▸ Algebra.mem_top
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; rw [hζfix]; rfl
    · intro r; exact hLfix r
    · intro a b _ _ ha hb; rw [map_add, ha, hb]; rfl
    · intro a b _ _ ha hb; rw [map_mul, ha, hb]; rfl
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hΦinj, by rw [hcardMK, Nat.card_prod]⟩

/-- **The cyclotomic character `autToPow L : Gal(M/L) → (ℤ/mℤ)ˣ` is a bijection.** Faithful
(`autToPow_injective`) and surjective by `|Gal(M/L)| = [M:L] = φ(m) = |(ℤ/mℤ)ˣ|`
(`cyclotomicField_finrank_eq` at base `L`). This is the `H ≅ (ℤ/mℤ)ˣ` half of C1's `G × H`
splitting; the master leaf uses its inverse to turn an admissible residue `τ` into the
`Gal(M/L)`-component of the compositum Frobenius. -/
private theorem autToPow_L_bijective
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hcop : ((NumberField.discr L).natAbs).Coprime m) (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective (hζ.autToPow L) := by
  haveI : FiniteDimensional K M := inferInstance
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have hML : Module.finrank L M = m.totient := cyclotomicField_finrank_eq L M m hcop
  have hcardML : Nat.card Gal(M/L) = Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank L M, hML, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hζ.autToPow_injective L, hcardML⟩

/-- Per-`τ` density of the crossing fibre (Sharifi 7.2.2 Step 2, p. 144, density `1/(|G|·|H|)`).
For `s ∈ Gal(M/K)` whose cyclic group meets `Gal(M/K(μ_m))` trivially (so `M/F` is cyclotomic at
`F = M^⟨s⟩`), the cyclotomic Frobenius-fibre asymptotic at `M/F` and `s`, lifted through `F/K` by
`density_lift_through_fixedField` gives the `s`-Frobenius fibre of `K` density
`1/(|G|·|H|)` — using `|carrier| = 1` (commutativity) and `|Gal(M/K)| = |G|·φ(m)`. -/
private theorem density_crossing_fibre_aux
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]
    [IsMulCommutative Gal(M/K)] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) (s : Gal(M/K))
    (hgate : Subgroup.zpowers s ⊓
      (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K M 𝔭 ∧
        frobeniusClass K M 𝔭 = ConjClasses.mk s}
      ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹) := by
  set F : IntermediateField K M := IntermediateField.fixedField (Subgroup.zpowers s) with hF
  haveI : IsScalarTower K ↥F M := F.isScalarTower_mid'
  haveI : IsCyclotomicExtension {m} ↥F M := by
    set Kμ : IntermediateField K M := IntermediateField.adjoin K {b : M | b ^ m = 1}
    obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
      IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
    have hadjζ : IntermediateField.adjoin K {ζ} = Kμ :=
      le_antisymm
        (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
          (IntermediateField.subset_adjoin K _ hζ.pow_eq_one)))
        (IntermediateField.adjoin_le_iff.mpr fun x hx ↦ by
          obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (Set.mem_setOf_eq ▸ hx)
          exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)) i)
    have hsup : (F ⊔ Kμ).fixingSubgroup = ⊥ := by
      rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField, hgate]
    have htop : F ⊔ Kμ = ⊤ := by
      have := congrArg IntermediateField.fixedField hsup
      rwa [IsGalois.fixedField_fixingSubgroup, IntermediateField.fixedField_bot] at this
    have htopF : IntermediateField.adjoin (↥F) {ζ} = ⊤ := by
      apply IntermediateField.restrictScalars_injective K
      rw [IntermediateField.restrictScalars_adjoin_eq_sup, hadjζ, htop]
      rfl
    haveI : Algebra.IsIntegral ↥F M := Algebra.IsIntegral.of_finite ↥F M
    haveI hcyc : IsCyclotomicExtension {m} ↥F (IntermediateField.adjoin (↥F) {ζ}) :=
      IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ↥F) hζ
    rw [htopF] at hcyc
    exact IsCyclotomicExtension.equiv (S := {m}) (A := ↥F) (f := IntermediateField.topEquiv)
  set σE : Gal(M/↥F) :=
    IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers s) ⟨s, Subgroup.mem_zpowers s⟩
  have hlift := density_lift_through_fixedField s F σE
    (by ext x; rfl) rfl (cyclotomic_density_from_two_sided_asymp ↥F M m hm4 σE)
  have hcarrier : Nat.card (ConjClasses.mk s).carrier = 1 := by
    letI : CommMonoid Gal(M/K) := IsMulCommutative.instCommMonoid
    have hcar : (ConjClasses.mk s).carrier = {s} := by
      ext a
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
        isConj_iff_eq, Set.mem_singleton_iff]
    rw [hcar, Nat.card_coe_set_eq, Set.ncard_singleton]
  have hcardMK : Nat.card Gal(M/K) = Nat.card Gal(L/K) * Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, cyclotomicField_finrank_eq L M m hcop,
      Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient]
  rw [hcarrier, hcardMK] at hlift
  simpa using hlift

/-- **Cyclotomic-crossing tagged master leaf** (Sharifi 7.2.2 Step 2, p. 144). For admissible
`m` (`hm4 : m % 4 ≠ 2`, `hcop : (disc L).natAbs.Coprime m`) and `σ ∈ G = Gal(L/K)`, there is a
single global tag `t : Ideal (𝓞 K) → (ℤ/mℤ)ˣ` — the `H`-component of the prime's
`Gal(M/K) = G × H`-Frobenius, `M = L(μ_m)` — and a family of prime sets `S_{σ,τ}` indexed by
`τ ∈ H_n = {τ : |G| ∣ ord τ}` such that:
* each `S_{σ,τ}` lies in the `σ`-Frobenius fibre of `K` by restriction;
* every prime of `S_{σ,τ}` has tag exactly `τ` (its `M`-Frobenius `H`-component);
* each `S_{σ,τ}` has Dirichlet density `1/(|G|·|H|)` (the cyclotomic asymptotic ratio at `M/F` with
  `F = M^⟨(σ,τ)⟩`, C3, lifted through `F/K` by `density_lift_through_fixedField`, C5).

The global tag makes the distinct-`τ` fibres disjoint by injectivity, which is the
only extra fact `exists_cyclotomicCrossing_fibres` needs on top of this leaf.

This packages the compositum infrastructure (`compositum_charProd_bijective` /
`autToPow_L_bijective` (C1), `cyclotomicField_finrank_eq` (C2a)) and the per-`τ` density chain
(C3/C4/C5); see the decomposition note above. `hm4`/`hcop` are threaded verbatim into those
leaves. -/
private theorem exists_crossing_family_tagged
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    ∃ (t : Ideal (𝓞 K) → (ZMod m)ˣ)
      (S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K))),
      (∀ τ, S τ ⊆ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ}) ∧
      (∀ τ, ∀ 𝔭 ∈ S τ, t 𝔭 = (τ : (ZMod m)ˣ)) ∧
      (∀ τ, HasDirichletDensity (S τ)
          ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹)) := by
  classical
  haveI : NeZero m := ⟨by lia⟩
  let M := CyclotomicField m L
  haveI : IsGalois K M := by
    obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
      IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
    haveI : FiniteDimensional K M := inferInstance
    haveI hsep : Algebra.IsSeparable K M := inferInstance
    set A : IntermediateField K M := (IsScalarTower.toAlgHom K L M).fieldRange with hA
    set B : IntermediateField K M := IntermediateField.adjoin K {ζ} with hB
    haveI hAnormal : Normal K A :=
      Normal.of_algEquiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L M))
    haveI hBcyc : IsCyclotomicExtension {m} K B :=
      hζ.intermediateField_adjoin_isCyclotomicExtension (K := K)
    haveI hBgal : IsGalois K B := IsCyclotomicExtension.isGalois (S := {m}) (K := K) (L := B)
    haveI hBnormal : Normal K B := hBgal.to_normal
    have hsup : A ⊔ B = ⊤ := by
      have hζalg : IsAlgebraic K ζ := Algebra.IsAlgebraic.isAlgebraic ζ
      have hsubalg : (IsScalarTower.toAlgHom K L M).range ⊔ Algebra.adjoin K {ζ}
          = (⊤ : Subalgebra K M) := by
        have htop : (Algebra.adjoin L {ζ} : Subalgebra L M) = ⊤ :=
          IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ
        rw [← Algebra.Subalgebra.restrictScalars_adjoin (R := K) (S := L) (s := {ζ}), htop,
          Subalgebra.restrictScalars_top]
      apply IntermediateField.toSubalgebra_injective
      rw [hA, hB, IntermediateField.sup_toSubalgebra_of_isAlgebraic_left,
        IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg,
        AlgHom.fieldRange_toSubalgebra, IntermediateField.top_toSubalgebra]
      exact hsubalg
    haveI hnormal : Normal K M := by
      have h := IntermediateField.normal_sup K M A B
      rw [hsup] at h
      exact Normal.of_algEquiv (IntermediateField.topEquiv (F := K) (E := M))
    exact IsGalois.mk
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  haveI : FiniteDimensional K M := inferInstance
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  set χK : Gal(M/K) →* (ZMod m)ˣ := hζ.autToPow K with hχK
  have hΦbij : Function.Bijective ((AlgEquiv.restrictNormalHom L).prod χK) :=
    compositum_charProd_bijective K L M m hcop ζ hζ
  set equivΦ : Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ :=
    MulEquiv.ofBijective _ hΦbij with hequivΦ
  set e2 : Gal(M/L) ≃* (ZMod m)ˣ :=
    MulEquiv.ofBijective (hζ.autToPow L) (autToPow_L_bijective K L M m hcop ζ hζ) with he2
  haveI : IsMulCommutative Gal(M/L) :=
    .of_comm fun a b ↦ e2.injective (by rw [map_mul, map_mul]; exact mul_comm (e2 a) (e2 b))
  haveI hGcomm : ∀ x y : Gal(L/K), x * y = y * x := fun x y ↦ mul_comm' x y
  haveI : IsMulCommutative Gal(M/K) :=
    .of_comm fun a b ↦ equivΦ.injective (by
      rw [map_mul, map_mul, Prod.mul_def, Prod.mul_def, hGcomm, mul_comm
        ((equivΦ a).2) ((equivΦ b).2)])
  set σM : (ZMod m)ˣ → Gal(M/K) := fun τ ↦ equivΦ.symm (σ, τ) with hσM
  have hσMpair : ∀ τ, (AlgEquiv.restrictNormalHom L (σM τ), χK (σM τ)) = (σ, τ) :=
    fun τ ↦ equivΦ.apply_symm_apply (σ, τ)
  have hσMrestr : ∀ τ, AlgEquiv.restrictNormalHom L (σM τ) = σ :=
    fun τ ↦ congrArg Prod.fst (hσMpair τ)
  have hσMchar : ∀ τ, χK (σM τ) = τ :=
    fun τ ↦ congrArg Prod.snd (hσMpair τ)
  refine ⟨fun 𝔭 ↦ χK (frobeniusClass K M 𝔭).out,
    fun τ ↦ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K M 𝔭 ∧
      frobeniusClass K M 𝔭 = ConjClasses.mk (σM τ)}, ?_, ?_, ?_⟩
  · rintro τ 𝔭 ⟨hp, hunrM, hfr⟩
    have hunrL : UnramifiedIn K L 𝔭 := (show ∀ (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K M 𝔭), (UnramifiedIn K L 𝔭) from by
      intro 𝔭 hunr
      classical
      haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
      refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
      haveI := h𝔮max
      haveI := h𝔮lo
      haveI h𝔮p : 𝔮.IsPrime := h𝔮max.isPrime
      have h𝔮bot : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔮
      obtain ⟨𝔓, _, h𝔓p, h𝔓comap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 M) 𝔮 ⊥ (by simp)
      haveI := h𝔓p
      haveI h𝔓lo𝔮 : 𝔓.LiesOver 𝔮 := ⟨h𝔓comap.symm⟩
      have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔮bot 𝔓
      haveI h𝔓max : 𝔓.IsMaximal := h𝔓p.isMaximal h𝔓bot
      have h𝔮under : Ideal.under (𝓞 L) 𝔓 = 𝔮 := h𝔓lo𝔮.over.symm
      have h𝔭under : Ideal.under (𝓞 K) 𝔮 = 𝔭 := h𝔮lo.over.symm
      haveI h𝔓lo𝔭 : 𝔓.LiesOver 𝔭 := ⟨by rw [← h𝔭under, ← h𝔮under, Ideal.under_under]⟩
      have hunderP : Ideal.under (𝓞 K) 𝔓 = 𝔭 := h𝔓lo𝔭.over.symm
      have hP1 : (Ideal.under (𝓞 K) 𝔓).ramificationIdx' 𝔓 = 1 := by
        rw [Ideal.ramificationIdx'_eq_ramificationIdx _ 𝔓 (hunderP ▸ hunr.1)]
        exact Ideal.ramificationIdx_eq_one_iff.mpr (hunr.2 𝔓 h𝔓max h𝔓lo𝔭)
      rw [hunderP] at hP1
      have htower := Ideal.ramificationIdx_algebra_tower (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 M)
        (p := 𝔭) (P := 𝔮) (Q := 𝔓) (Ideal.map_ne_bot_of_ne_bot h𝔮bot)
        (Ideal.map_ne_bot_of_ne_bot hunr.1) (by rw [Ideal.map_le_iff_le_comap]; exact h𝔓comap.ge)
      rw [hP1] at htower
      have he𝔮 : 𝔭.ramificationIdx' 𝔮 = 1 := Nat.eq_one_of_mul_eq_one_right htower.symm
      rw [← Ideal.ramificationIdx_eq_one_iff,
        ← Ideal.ramificationIdx'_eq_ramificationIdx 𝔭 𝔮 hunr.1]
      exact he𝔮) 𝔭 hunrM
    exact ⟨hp, hunrL,
      (show ∀ (σ : Gal(L/K)) (τM : Gal(M/K)) (_hτM : AlgEquiv.restrictNormalHom L τM = σ) (𝔭 : Ideal (𝓞 K)) (_hunrM : UnramifiedIn K M 𝔭) (_hunrL : UnramifiedIn K L 𝔭) (_hfr : frobeniusClass K M 𝔭 = ConjClasses.mk τM), (frobeniusClass K L 𝔭 = ConjClasses.mk σ) from by
        intro σ τM _hτM 𝔭 _hunrM _hunrL _hfr
        classical
        by_cases hp : 𝔭.IsPrime
        · haveI := hp
          exact (show ∀ (σ : Gal(L/K)) (τM : Gal(M/K)) (_hτM : AlgEquiv.restrictNormalHom L τM = σ) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (_hunrM : UnramifiedIn K M 𝔭) (_hunrL : UnramifiedIn K L 𝔭) (_hfr : frobeniusClass K M 𝔭 = ConjClasses.mk τM), (frobeniusClass K L 𝔭 = ConjClasses.mk σ) from by
            intro σ τM _hτM 𝔭 root119Instance0 _hunrM _hunrL _hfr
            classical
            obtain ⟨𝔓, h𝔓p, hcomap⟩ :=
              Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 M) 𝔭 (by
                rw [(RingHom.injective_iff_ker_eq_bot _).mp
                  (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 M))]
                exact bot_le)
            have h𝔓lo : 𝔓.LiesOver 𝔭 := ⟨hcomap.symm⟩
            haveI := h𝔓p
            haveI := h𝔓lo
            haveI : Finite (𝓞 M ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
              (Ideal.ne_bot_of_liesOver_of_ne_bot _hunrM.1 𝔓)
            set σM : Gal(M/K) := arithFrobAt (𝓞 K) Gal(M/K) 𝔓
            have hMfrobσM : IsArithFrobAt (𝓞 K) σM 𝔓 := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(M/K) 𝔓
            have hclassM : frobeniusClass K M 𝔭 = ConjClasses.mk σM := by
              let e : ∃ 𝔔 : Ideal (𝓞 M), 𝔔.IsPrime ∧ 𝔔.LiesOver 𝔭 := by
                obtain ⟨𝔔, hq, hcomap'⟩ :=
                  Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 M) 𝔭 (by
                    rw [(RingHom.injective_iff_ker_eq_bot _).mp
                      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 M))]
                    exact bot_le)
                exact ⟨𝔔, hq, ⟨hcomap'.symm⟩⟩
              let 𝔔 := Classical.choose e
              haveI : 𝔔.IsPrime := (Classical.choose_spec e).1
              have hqlo : 𝔔.LiesOver 𝔭 := (Classical.choose_spec e).2
              haveI : Finite (𝓞 M ⧸ 𝔔) := Ideal.finiteQuotientOfFreeOfNeBot 𝔔
                (Ideal.ne_bot_of_liesOver_of_ne_bot _hunrM.1 𝔔)
              rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, _hunrM⟩]
              change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(M/K) 𝔔) = ConjClasses.mk σM
              exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
                isConj_arithFrobAt (𝓞 K) Gal(M/K) 𝔔 𝔓 (hqlo.over.symm.trans h𝔓lo.over)
            have hconjM : IsConj σM τM := ConjClasses.mk_eq_mk_iff_isConj.mp
              (hclassM.symm.trans _hfr)
            haveI : (𝔓.under (𝓞 L)).IsPrime := Ideal.IsPrime.under (𝓞 L) 𝔓
            haveI : (𝔓.under (𝓞 L)).LiesOver 𝔭 := ⟨((Ideal.under_under 𝔓).trans h𝔓lo.over.symm).symm⟩
            have hσL : IsArithFrobAt (𝓞 K) (σM.restrictNormal L) (𝔓.under (𝓞 L)) :=
              (show ∀ (σ : Gal(M/K)) (𝔓 : Ideal (𝓞 M)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓), (IsArithFrobAt (𝓞 K) (σ.restrictNormal L) (𝔓.under (𝓞 L))) from by
                intro σ 𝔓 hσ
                classical
                haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
                have hunder : (𝔓.under (𝓞 L)).under (𝓞 K) = 𝔓.under (𝓞 K) := Ideal.under_under 𝔓
                intro y
                rw [hunder, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
                  MulSemiringAction.toAlgHom_apply, ← (show ∀ (σ : Gal(M/K)) (y : 𝓞 L), (σ • (algebraMap (𝓞 L) (𝓞 M) y) = algebraMap (𝓞 L) (𝓞 M) ((σ.restrictNormal L) • y)) from by
                    intro σ y
                    classical
                    haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
                    have hbridgeM : ∀ (g : M ≃ₐ[K] M) (x : 𝓞 M), ((g • x : 𝓞 M) : M) = g • (x : M) := fun g x ↦
                      by simpa [Algebra.smul_def] using
                        (smul_distrib_smul (G := M ≃ₐ[K] M) (R := 𝓞 M) (S := M) g x 1).symm
                    have hbridgeL : ∀ (g : L ≃ₐ[K] L) (z : 𝓞 L), ((g • z : 𝓞 L) : L) = g • ((z : L)) := fun g z ↦
                      by simpa [Algebra.smul_def] using
                        (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g z 1).symm
                    have hcoe : ∀ z : 𝓞 L, ((algebraMap (𝓞 L) (𝓞 M) z : 𝓞 M) : M) = algebraMap L M (z : L) :=
                      fun z ↦ by
                        rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 M) M,
                          RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 L) L M]
                    rw [RingOfIntegers.ext_iff, hbridgeM, hcoe y, hcoe ((σ.restrictNormal L) • y), hbridgeL,
                      AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]) σ y]
                exact hσ (algebraMap (𝓞 L) (𝓞 M) y)) σM 𝔓 hMfrobσM
            haveI : Finite (𝓞 L ⧸ 𝔓.under (𝓞 L)) :=
              Ideal.finiteQuotientOfFreeOfNeBot _
                (Ideal.ne_bot_of_liesOver_of_ne_bot _hunrL.1 (𝔓.under (𝓞 L)))
            have hclassL : frobeniusClass K L 𝔭 =
                ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) (𝔓.under (𝓞 L))) := by
              let e : ∃ 𝔔 : Ideal (𝓞 L), 𝔔.IsPrime ∧ 𝔔.LiesOver 𝔭 := by
                obtain ⟨𝔔, hq, hcomap'⟩ :=
                  Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
                    rw [(RingHom.injective_iff_ker_eq_bot _).mp
                      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
                    exact bot_le)
                exact ⟨𝔔, hq, ⟨hcomap'.symm⟩⟩
              let 𝔔 := Classical.choose e
              haveI : 𝔔.IsPrime := (Classical.choose_spec e).1
              have hqlo : 𝔔.LiesOver 𝔭 := (Classical.choose_spec e).2
              haveI : Finite (𝓞 L ⧸ 𝔔) := Ideal.finiteQuotientOfFreeOfNeBot 𝔔
                (Ideal.ne_bot_of_liesOver_of_ne_bot _hunrL.1 𝔔)
              haveI : Finite (𝓞 L ⧸ 𝔓.under (𝓞 L)) := Ideal.finiteQuotientOfFreeOfNeBot _
                (Ideal.ne_bot_of_liesOver_of_ne_bot _hunrL.1 (𝔓.under (𝓞 L)))
              rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, _hunrL⟩]
              change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔔) =
                ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) (𝔓.under (𝓞 L)))
              exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
                isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔔 (𝔓.under (𝓞 L))
                  (hqlo.over.symm.trans (‹(𝔓.under (𝓞 L)).LiesOver 𝔭›).over)
            have hqbot := Ideal.ne_bot_of_liesOver_of_ne_bot _hunrL.1 (𝔓.under (𝓞 L))
            haveI : Finite (𝓞 L ⧸ 𝔓.under (𝓞 L)) := Ideal.finiteQuotientOfFreeOfNeBot _ hqbot
            haveI : Algebra.IsUnramifiedAt (𝓞 K) (𝔓.under (𝓞 L)) :=
              _hunrL.2 _ (‹(𝔓.under (𝓞 L)).IsPrime›.isMaximal hqbot) inferInstance
            letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
            have hσeq : σM.restrictNormal L =
                arithFrobAt (𝓞 K) Gal(L/K) (𝔓.under (𝓞 L)) :=
              MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
                AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσL
                  (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) (𝔓.under (𝓞 L)))
                  (𝔓.under (𝓞 L)).primeCompl_le_nonZeroDivisors
            rw [hclassL, ← hσeq]
            refine ConjClasses.mk_eq_mk_iff_isConj.mpr ?_
            have hconjL := MonoidHom.map_isConj (AlgEquiv.restrictNormalHom L) hconjM
            rwa [_hτM] at hconjL) σ τM _hτM 𝔭 _hunrM _hunrL _hfr
        · have hMjunk : frobeniusClass K M 𝔭 = ConjClasses.mk 1 := by
            rw [frobeniusClass, dif_neg fun h ↦ hp h.1]
          have hLjunk : frobeniusClass K L 𝔭 = ConjClasses.mk 1 := by
            rw [frobeniusClass, dif_neg fun h ↦ hp h.1]
          have hconj : IsConj (1 : Gal(M/K)) τM :=
            ConjClasses.mk_eq_mk_iff_isConj.mp (hMjunk.symm.trans _hfr)
          have hτM1 : τM = 1 := isConj_one_right.mp hconj
          have hσ1 : σ = 1 := by rw [← _hτM, hτM1, map_one]
          rw [hLjunk, hσ1]) σ (σM τ) (hσMrestr τ) 𝔭 hunrM hunrL hfr⟩
  · rintro τ 𝔭 ⟨-, -, hfr⟩
    have hconj : IsConj (frobeniusClass K M 𝔭).out (σM (τ : (ZMod m)ˣ)) := by
      rw [hfr]
      exact ConjClasses.mk_eq_mk_iff_isConj.mp (Quotient.out_eq _)
    change χK (frobeniusClass K M 𝔭).out = (τ : (ZMod m)ˣ)
    rw [isConj_iff_eq.mp (χK.map_isConj hconj), hσMchar]
  · rintro ⟨τ, hτ⟩
    exact density_crossing_fibre_aux K L M m hm4 hcop (σM τ)
      ((show ∀ (m : ℕ) [NeZero m] (ζ : M) (hζ : IsPrimitiveRoot ζ m) (σ : Gal(L/K)) (τ : (ZMod m)ˣ) (hτ : Nat.card Gal(L/K) ∣ orderOf τ) (s : Gal(M/K)) (hsrestr : AlgEquiv.restrictNormalHom L s = σ) (hschar : hζ.autToPow K s = τ) (hΦbij : Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K))), (Subgroup.zpowers s ⊓ (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) from by
        intro m root119Instance0 ζ hζ σ τ hτ s hsrestr hschar hΦbij
        classical
        rw [eq_bot_iff]
        rintro g hg
        rw [Subgroup.mem_inf] at hg
        obtain ⟨⟨k, hk⟩, hgfix⟩ := hg
        simp only at hk
        have hgζ : g ζ = ζ :=
          (IntermediateField.mem_fixingSubgroup_iff _ g).mp hgfix ζ <|
            IntermediateField.subset_adjoin K _ hζ.pow_eq_one
        have hχg : hζ.autToPow K g = 1 := (show ∀ (m : ℕ) [NeZero m] (ζ : M) (hζ : IsPrimitiveRoot ζ m) (g : Gal(M/K)) (hg : g ζ = ζ), (hζ.autToPow K g = 1) from by
          intro m root119Instance0 ζ hζ g hg
          classical
          have hspec := hζ.autToPow_spec K g
          rw [hg] at hspec
          set u : (ZMod m)ˣ := hζ.autToPow K g with hu
          have hmod : (u : ZMod m).val ≡ 1 [MOD m] := by
            have hisu : IsUnit ζ := hζ.isUnit (NeZero.ne m)
            lift ζ to Mˣ using hisu with z hz
            have hzp : IsPrimitiveRoot z m := by rwa [IsPrimitiveRoot.coe_units_iff] at hζ
            have hord : orderOf z = m := (IsPrimitiveRoot.eq_orderOf hzp).symm
            have h' : z ^ (u : ZMod m).val = z ^ (1 : ℕ) := by
              apply Units.ext
              push_cast
              rwa [pow_one]
            rwa [pow_eq_pow_iff_modEq, hord] at h'
          have hu1 : (u : ZMod m) = 1 := by
            have hcast : ((u : ZMod m).val : ZMod m) = (1 : ZMod m) := by
              rw [← Nat.cast_one]
              exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
            rwa [ZMod.natCast_val, ZMod.cast_id] at hcast
          exact Units.ext hu1) m ζ hζ g hgζ
        have hχgτ : τ ^ k = 1 := by
          rw [← hschar, ← map_zpow, hk]
          exact hχg
        have hGk : (Nat.card Gal(L/K) : ℤ) ∣ k :=
          dvd_trans (Int.natCast_dvd_natCast.mpr hτ) (orderOf_dvd_iff_zpow_eq_one.mpr hχgτ)
        have hσk : σ ^ k = 1 :=
          orderOf_dvd_iff_zpow_eq_one.mp
            (dvd_trans (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard σ)) hGk)
        have hrestrg : AlgEquiv.restrictNormalHom L g = 1 := by rw [← hk, map_zpow, hsrestr, hσk]
        rw [Subgroup.mem_bot]
        apply hΦbij.injective
        rw [MonoidHom.prod_apply, MonoidHom.prod_apply, hrestrg, hχg, map_one, map_one]) m ζ hζ σ τ hτ (σM τ) (hσMrestr τ)
        (hσMchar τ) hΦbij)

theorem exists_cyclotomicCrossing_fibres
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    ∃ S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K)),
      (Set.univ : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S ∧
      (∀ τ, S τ ⊆ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ}) ∧
      (∀ τ, HasDirichletDensity (S τ)
          ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹)) := by
  obtain ⟨t, S, hsub, htag, hd⟩ := exists_crossing_family_tagged K L σ m hm hm4 hcop
  exact ⟨S, (show ∀ (t : (Ideal (𝓞 K)) → ((ZMod m)ˣ)) (f : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → ((ZMod m)ˣ)) (hf : Function.Injective f) (S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K))) (htag : ∀ i, ∀ a ∈ S i, t a = f i), ((Set.univ : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S) from by
    intro t f hf S htag
    classical
    intro i _ j _ hij
    simp only [Function.onFun, Set.disjoint_left]
    intro a hi hj
    exact hij (hf ((htag i a hi).symm.trans (htag j a hj)))) t Subtype.val Subtype.val_injective S htag, hsub, hd⟩

end Chebotarev
