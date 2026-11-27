/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Places/TameInertia
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Places/TameInertia
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Places.TameInertia. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Places/TameInertia.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology.SylowReduction
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Structure of tame inertia: acts through roots of uniformiser, Frobenius acts by q. -/


open Polynomial IsSepClosed MulAction Subgroup Set QuotientGroup Finset
variable {Γ k Ω} [Group Γ] [Field k] [Field Ω] [Algebra k Ω] [MulSemiringAction Γ Ω] {A :
  ValuationSubring Ω} {π : kˣ} (hπ : IsUniformiser A π.1) {s} (hs : s ∈ inertiaGroup Γ A) {n : ℕ}
  (hn : A.valuation n = 1) {y} (hy : y ^ n = algebraMap k Ω π)

section

include hs

lemma valuation_smul_div_sub_one_lt_one {w} (v : A w = 1) : A (s • w / w - 1) < 1 := by
  simpa [*, div_sub_one, ← A.valuation.zero_iff] using hs.2 w

include hn

/-- Let s lie in the inertia group of A and let n be a unit of A. If w^n is a unit of A fixed by
s, then s·w / w = 1. -/
lemma inertia_fixes_root_of_unit {w u} (r : w ^ n = u) (v : A.valuation u = 1) (e : s • u = u) :
  s • w = w := eq_of_div_eq_one (by apply eq_of_val_sub_lt_one hn <;> aesop (add simp [div_pow,
  valuation_smul_div_sub_one_lt_one]))

include hy

omit hs in
lemma ne_zero_of_tame_root : y ≠ 0 ∧ NeZero n := by
  cases n <;> grind [NeZero, map_eq_zero, Units, zero_ne_one]

lemma smul_root_eq_ratio_mul {b} (hb : b ^ n = algebraMap k Ω π) : s • b = s • y / y * b := by
  grind [inertia_fixes_root_of_unit hs hn (div_pow y b n), smul_mul', → ne_zero_of_tame_root,
    smul_one, pow_ne_zero]

lemma inertia_pow_smul_div [SMulCommClass Γ k Ω]
    i : s ^ i • y / y = (s • y / y) ^ i := by induction i <;> simp [*,
          ne_zero_of_tame_root hn hy, pow_succ', mul_smul, ← smul_pow', ← mul_div,
  smul_root_eq_ratio_mul (b := _ • y) hs hn hy]

end

include hπ
variable [TopologicalSpace Γ] [G : IsLocalGalois Γ k A]

lemma IsLocalGalois.exists_valuation_pow_inertia_index (_ : y ≠ 0) : ∃ d : ℤ,
  A y ^ (stabilizer (inertiaGroup Γ A) y).index = valuationVia k A π ^
  d := have ⟨⟨c, e⟩, h⟩ := exists_val_eq_pow_index (Γ := inertiaGroup Γ A) (·.2.1) y
  h ▸ (G.exists_ordRat_eq_intCast (x :=
    .mk0 c (by simpa [·, valuationVia, *] using h.ge)) (DiscreteUnits.ext <| e ⟨·, ·⟩)).imp fun d ↦
    by simpa using! (hπ.val_pow_eq_iff_mul_ordRat G 1 _).2

/-- Over a local field with uniformiser π, let x^n have the valuation of π and let the inertia
orbit of x lie in a set T of at most n elements. Then every y in T is in that orbit. -/
lemma exists_inertia_smul_eq_of_orbit_subset {x y T n} (hn : #T ≤ n) (hx : valuationVia k A π =
  A x ^ n) (h : ∀ g : inertiaGroup Γ A, g.1 • x ∈ T) (hy : y ∈ T) : ∃ g ∈ inertiaGroup Γ A, g • x =
  y := have : x ≠ 0 ∧ A x ≠ 1 := hπ.val_lt_one.rec (by cases n <;> aesop)
  by simpa using (eq_of_subset_of_ncard_le (forall_mem_range.2 h) (mod_cast hn.trans (n.le_of_dvd
    ((nonempty_orbit x).ncard_pos (isLocallyConstant_smul x).range_finite) (by
      simpa [*, ← zpow_natCast, ← zpow_mul, zero_lt_iff, ← Int.ofNat_dvd, index_stabilizer]
      using! G.exists_valuation_pow_inertia_index hπ this.1)))).ge hy

lemma IsLocalGalois.exists_inertia_smul_eq_of_pow_eq {x y n} (hn : 0 < n) (hx : x ^ n =
  algebraMap k Ω π) (hy : y ^ n = x ^ n) : ∃ g ∈ inertiaGroup Γ A, g • x =
  y := by apply exists_inertia_smul_eq_of_orbit_subset hπ ((Multiset.toFinset_card_le _).trans
  (card_nthRoots n (x ^ n))) <;> simp_all [← smul_pow', ← map_pow]

include hn hy

/-- Let n be a unit of A, yⁿ a uniformiser of k, f on inertia with open kernel and fⁿ = 1. Then
f kills the stabiliser of y, f(s) generates the image if sy/y has order n, and f(φsφ⁻¹) =
f(s)^q for a q-Frobenius φ.

Known result: Hilbert ramification theory for infinite Galois extensions; ideles and ideal
classes. -/
lemma IsLocalGalois.tame_inertia {P} [Monoid P] (f : inertiaGroup Γ A →* P) (hf : f.ker.IsOpen)
  (hP : ∀ g, f g ^ n = 1) : stabilizer _ y ≤ f.ker ∧ ∀ s, (IsPrimitiveRoot (s • y / y) n → ∀ g, ∃ i,
  f g = f s ^ i) ∧ ∀ q φ, IsFrob A q φ → ∃ h, f ⟨φ * s * φ⁻¹, h⟩ = f s ^ q := by
  obtain ⟨⟨⟩, ⟨M, l⟩⟩ := ne_zero_of_tame_root hn hy, @IsPGroup.exists_card_dvd_pow n _ _
    (quotient_finite_of_isOpen _ hf) (⟨1, ·.ind' (by simp [← mk_pow, *])⟩), Fact.mk hf
  use ?K, fun s ↦ have E g i (e : g.1 • y / y = (s.1 • y / y) ^ i) : f g = f s ^ i := (f.eq_iff.2
    (?K (by simp_all [mul_smul, ← inertia_pow_smul_div _ hn hy,
      Subgroup.smul_def]))).trans (map_pow ..)
    ⟨fun h g ↦ (h.eq_pow_of_pow_eq_one (by simp [div_pow, ← smul_pow', *])).imp (E g · ·.2.symm),
    fun q φ h ↦ ⟨(h.1 ▸ s.2.conj φ :), E _ _ (by simp [smul_root_eq_ratio_mul (b := _ • y) _ hn hy,
      ← smul_pow', *, mul_smul, div_pow, ← cycCharMod_eq_iff.1 (h.cycCharMod_eq hn)])⟩⟩
  obtain ⟨y, rfl⟩ := exists_pow_nat_eq y (n ^ M)
  intro r h
  rw [← pow_mul] at hy
  obtain ⟨⟨ξ⟩, _, ⟨⟩⟩ := exists_pow_nat_eq (r • y / y) n,
    ne_zero_of_tame_root (A := A) (by aesop) hy
  exact (G.exists_inertia_smul_eq_of_pow_eq hπ (y :=
    ξ * y) Fin.pos' hy (by simp_all [mul_pow, pow_mul', div_pow])).rec fun t ⟨a, _⟩ ↦
    .trans (f.eq_iff.2 ((fun r h ↦ (fixingSubgroup_fixedFieldOf _).le fun ⟨x, hx⟩ ↦ by_contra
    (((index_dvd_of_le (K := stabilizer ..) (sub_mem (smul_mem_fixedPoints_of_normal r hx) hx ⟨·,
    ·⟩)).trans (l.mul_right n)).rec (fun m _ ⟨d, _⟩ ↦ (A.valuation.map_sum_lt' (s := range n)
    one_pos fun i _ ↦ valuation_smul_div_sub_one_lt_one (r ^ i).2 (w := (r • x - x) / y ^ (m * d))
    (by simp_all [← hy, zpow_mul, zpow_comm, zpow_left_inj₀, zpow_ne_zero, valuationVia,
    ← zpow_natCast])).ne (by simp_all [smul_eq_self_of_mem_zpowers _ h, smul_div₀', ← pow_succ,
    ← sum_div, smul_sub, smul_smul, ↓← Subgroup.smul_def, sum_range_sub (r ^ · • x),
    (f.ker.mk_smul · · x ▸ hx _)])) ∘ G.exists_valuation_pow_inertia_index
    hπ ∘ sub_ne_zero.2) : stabilizer _ y ≤ _) _ (by simpa [inv_smul_eq_iff, *, mul_smul] using!
    (inertia_pow_smul_div a (by aesop) hy n).symm))) (f.map_pow .. ▸ hP ⟨t, a⟩)
