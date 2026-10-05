/- GID: D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Construction/ConstructionA
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construction A lattices, covolumes and ellipsoid transfer. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib

open Finset
open Submodule
open Module

namespace D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA

variable {p n : ℕ}

/-- Coordinatewise reduction `ℤⁿ → (ZMod p)ⁿ`. -/
def redMod (p : ℕ) {n : ℕ} (y : Fin n → ℤ) : Fin n → ZMod p := fun i => ((y i : ℤ) : ZMod p)

/-- Construction A with `k = 1`: the residue `v` lies on the line `C_g = ⟨g⟩`. -/
def OnLine {p n : ℕ} (g v : Fin n → ZMod p) : Prop := ∃ u : ZMod p, u • g = v

instance decidableOnLine [NeZero p] (g v : Fin n → ZMod p) : Decidable (OnLine g v) := by
  unfold OnLine; infer_instance

theorem onLine_zero_iff [NeZero p] (v : Fin n → ZMod p) : OnLine 0 v ↔ v = 0 := by
  constructor
  · rintro ⟨u, hu⟩; rw [← hu, smul_zero]
  · rintro rfl; exact ⟨0, smul_zero 0⟩

/-- **The line count.** A nonzero residue lies on exactly `p - 1` lines `⟨g⟩`. -/
theorem card_filter_onLine [Fact (Nat.Prime p)] (v : Fin n → ZMod p) (hv : v ≠ 0) :
    (Finset.univ.filter (fun g : Fin n → ZMod p => OnLine g v)).card = p - 1 := by
  classical
  have hset : (Finset.univ.filter (fun g : Fin n → ZMod p => OnLine g v))
      = (Finset.univ.erase (0 : ZMod p)).image (fun u : ZMod p => u • v) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨u, hu⟩
      have hu0 : u ≠ 0 := by rintro rfl; exact hv (by rw [← hu, zero_smul])
      exact ⟨u⁻¹, ⟨inv_ne_zero hu0, trivial⟩, by
        rw [← hu, smul_smul, inv_mul_cancel₀ hu0, one_smul]⟩
    · rintro ⟨u, ⟨hu0, -⟩, rfl⟩
      exact ⟨u⁻¹, by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]⟩
  rw [hset, Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card]
  intro a _ b _ hab
  set_option backward.isDefEq.respectTransparency false in
    exact smul_left_injective (ZMod p) hv hab

/-- **First-moment lemma (exact form).**  Summing over *all* `g`, the total number of
incidences between a finite set `A` of `p`-indivisible integer points and the lines `⟨g⟩`
is exactly `(p - 1) * |A|`.  This is the swap of two finite sums. -/
theorem sum_card_filter_onLine [Fact (Nat.Prime p)] (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) :
    ∑ g : Fin n → ZMod p, (A.filter (fun y => OnLine g (redMod p y))).card
      = (p - 1) * A.card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun y hy => ?_)]
  · rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · show ∑ g : Fin n → ZMod p, (if OnLine g (redMod p y) then 1 else 0) = p - 1
    rw [← Finset.card_filter]
    exact card_filter_onLine _ (hA y hy)

/-- The `g = 0` line carries no `p`-indivisible point, so the sum over `g ≠ 0` is the same. -/
theorem sum_card_filter_onLine_erase [Fact (Nat.Prime p)] (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) :
    ∑ g ∈ Finset.univ.erase (0 : Fin n → ZMod p),
        (A.filter (fun y => OnLine g (redMod p y))).card
      = (p - 1) * A.card := by
  classical
  rw [← sum_card_filter_onLine A hA, eq_comm,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n → ZMod p))]
  have hzero : (A.filter (fun y => OnLine (0 : Fin n → ZMod p) (redMod p y))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hcon
    exact hA y hy ((onLine_zero_iff _).1 hcon)
  rw [hzero, add_zero]

theorem succ_le_pow (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (p - 1) * p ^ (n - 1) + 1 ≤ p ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : (p - 1) * p ^ k + p ^ k = p * p ^ k := by
    cases p with
    | zero => omega
    | succ q => simp; ring
  simp only [Nat.add_sub_cancel]
  rw [pow_succ, mul_comm (p ^ k) p]
  omega

/-- **The density bound, division-free.**  `p^{n-1} · Σ_{g≠0} (count) ≤ (pⁿ - 1) · |A|`,
i.e. the average over the `pⁿ - 1` nonzero `g` is at most `|A| · p^{1-n}`. -/
theorem sum_card_le [Fact (Nat.Prime p)] (hn : 1 ≤ n) (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) :
    p ^ (n - 1) * (∑ g ∈ Finset.univ.erase (0 : Fin n → ZMod p),
        (A.filter (fun y => OnLine g (redMod p y))).card)
      ≤ (p ^ n - 1) * A.card := by
  have hp : 1 ≤ p := (Fact.out (p := Nat.Prime p)).one_lt.le.trans' (by norm_num)
  rw [sum_card_filter_onLine_erase A hA]
  have key : (p - 1) * p ^ (n - 1) + 1 ≤ p ^ n := succ_le_pow hp hn
  have : p ^ (n - 1) * ((p - 1) * A.card) = ((p - 1) * p ^ (n - 1)) * A.card := by ring
  rw [this]
  exact Nat.mul_le_mul_right _ (by omega)

/-- **The union bound / selection step** (`1/2 + 1/e < 1`): if the two bad sets together
miss some element of `s`, a good `g` exists. -/
theorem exists_mem_not_mem {ι : Type*} [DecidableEq ι] {s B₁ B₂ : Finset ι}
    (h : B₁.card + B₂.card < s.card) : ∃ i ∈ s, i ∉ B₁ ∧ i ∉ B₂ := by
  classical
  have hne : (s \ (B₁ ∪ B₂)).Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (B₁ ∪ B₂).card ≤ B₁.card + B₂.card := Finset.card_union_le _ _
    have h2 : s.card - (B₁ ∪ B₂).card ≤ (s \ (B₁ ∪ B₂)).card := Finset.le_card_sdiff _ _
    omega
  obtain ⟨i, hi⟩ := hne
  rw [Finset.mem_sdiff, Finset.mem_union] at hi
  exact ⟨i, hi.1, fun hc => hi.2 (Or.inl hc), fun hc => hi.2 (Or.inr hc)⟩

/-- A nonzero integer point all of whose coordinates are divisible by `p` has a coordinate of
absolute value at least `p`.  This is why the `pℤⁿ` term of the first-moment lemma vanishes
identically once `p` exceeds the radius of the support. -/
theorem le_abs_of_dvd {y : Fin n → ℤ} (hdvd : ∀ i, (p : ℤ) ∣ y i) {j : Fin n} (hj : y j ≠ 0) :
    (p : ℤ) ≤ |y j| :=
  Int.le_of_dvd (abs_pos.2 hj) ((dvd_abs _ _).2 (hdvd j))

/-- The number of nonzero `g` is `pⁿ - 1`. -/
theorem card_erase_univ [NeZero p] :
    (Finset.univ.erase (0 : Fin n → ZMod p)).card = p ^ n - 1 := by
  classical
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  simp [ZMod.card]

/-- **Use 1's Markov step (eq. 64), discrete counterpart.**  The number of lines meeting the
finite set `A` at all is at most `(pⁿ-1)·|A|/p^{n-1}`. -/
theorem card_bad_one_le [Fact (Nat.Prime p)] (hn : 1 ≤ n) (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) :
    p ^ (n - 1) *
        ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => ∃ y ∈ A, OnLine g (redMod p y))).card
      ≤ (p ^ n - 1) * A.card := by
  classical
  refine le_trans (Nat.mul_le_mul_left _ ?_) (sum_card_le hn A hA)
  calc ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => ∃ y ∈ A, OnLine g (redMod p y))).card
      = ∑ _g ∈ (Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => ∃ y ∈ A, OnLine g (redMod p y)), 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ g ∈ (Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => ∃ y ∈ A, OnLine g (redMod p y)),
          (A.filter (fun y => OnLine g (redMod p y))).card := by
        refine Finset.sum_le_sum (fun g hg => ?_)
        obtain ⟨y, hy, hyg⟩ := (Finset.mem_filter.1 hg).2
        exact Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨hy, hyg⟩⟩
    _ ≤ ∑ g ∈ Finset.univ.erase (0 : Fin n → ZMod p),
          (A.filter (fun y => OnLine g (redMod p y))).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Generic sublattice criterion** (absent from Mathlib).  If `M ≤ L` with `L` a `ℤ`-lattice
and `M ⊇ k · L` for some `k ≠ 0`, then `M` is a `ℤ`-lattice. -/
theorem discreteTopology_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : Submodule ℤ E) [DiscreteTopology L] (hML : M ≤ L) :
    DiscreteTopology M :=
  DiscreteTopology.of_subset (s := (L : Set E)) inferInstance hML

theorem span_real_eq_top_of_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {k : ℕ} (hk : k ≠ 0) (hkL : ∀ x ∈ L, (k : ℤ) • x ∈ M) :
    Submodule.span ℝ (M : Set E) = ⊤ := by
  have hL : Submodule.span ℝ (L : Set E) = ⊤ := IsZLattice.span_top
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro x hx
  have h1 : ((k : ℤ) • x) ∈ M := hkL x hx
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have h2 : ((k : ℤ) • x : E) = (k : ℝ) • x := by
    rw [← Int.cast_smul_eq_zsmul ℝ]; norm_num
  have h3 : x = (k : ℝ)⁻¹ • ((k : ℝ) • x) := (inv_smul_smul₀ hk0 x).symm
  rw [SetLike.mem_coe, h3, ← h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

/-- The `ℤ`-linear inclusion `ℤⁿ ↪ ℝⁿ`. -/
def toReal (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) where
  toFun y := fun i => (y i : ℝ)
  map_add' y z := by funext i; simp
  map_smul' m y := by funext i; simp [zsmul_eq_mul]

theorem toReal_apply (y : Fin n → ℤ) (i : Fin n) : toReal n y i = (y i : ℝ) := rfl

theorem toReal_injective : Function.Injective (toReal n) := by
  intro y z h
  funext i
  have hi := congrFun h i
  rw [toReal_apply, toReal_apply] at hi
  exact_mod_cast hi

/-- Coordinatewise reduction `ℤⁿ → (ZMod p)ⁿ`, as a `ℤ`-linear map. -/
def redLin (p n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod p) where
  toFun y := fun i => ((y i : ℤ) : ZMod p)
  map_add' y z := by funext i; simp
  map_smul' m y := by funext i; simp [zsmul_eq_mul]

theorem redLin_apply (y : Fin n → ℤ) (i : Fin n) : redLin p n y i = ((y i : ℤ) : ZMod p) := rfl

theorem redLin_surjective [NeZero p] : Function.Surjective (redLin p n) := by
  intro v
  refine ⟨fun i => (ZMod.cast (v i) : ℤ), ?_⟩
  funext i
  simp [redLin_apply]

/-- The `p`-ary line `C_g = ⟨g⟩`, as a `ℤ`-submodule. -/
def lineZ (g : Fin n → ZMod p) : Submodule ℤ (Fin n → ZMod p) :=
  (Submodule.span (ZMod p) ({g} : Set (Fin n → ZMod p))).restrictScalars ℤ

/-- **Construction A in `ℤⁿ`**: `Λ₀(g) = {y ∈ ℤⁿ : y mod p ∈ ⟨g⟩}`. -/
def latZ (p n : ℕ) (g : Fin n → ZMod p) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.comap (redLin p n) (lineZ g)

theorem mem_latZ (g : Fin n → ZMod p) (y : Fin n → ℤ) :
    y ∈ latZ p n g ↔ ∃ u : ZMod p, u • g = redLin p n y := by
  simp only [latZ, Submodule.mem_comap, lineZ, Submodule.restrictScalars_mem,
    Submodule.mem_span_singleton]

/-- `Λ₀(g)` contains `p·ℤⁿ`. -/
theorem smul_mem_latZ (g : Fin n → ZMod p) (y : Fin n → ℤ) : (p : ℤ) • y ∈ latZ p n g := by
  rw [mem_latZ]
  refine ⟨0, ?_⟩
  rw [zero_smul]
  funext i
  simp [redLin_apply]

/-- The standard integer lattice in `ℝⁿ`. -/
def intLat (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

theorem intLat_eq_range (n : ℕ) : intLat n = LinearMap.range (toReal n) := by
  apply le_antisymm
  · rw [intLat, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨fun j => if j = i then 1 else 0, by
      funext j; simp [toReal_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]⟩
  · rintro _ ⟨y, rfl⟩
    have : toReal n y = ∑ i : Fin n, y i • (Pi.basisFun ℝ (Fin n)) i := by
      funext j
      simp [toReal_apply, Pi.basisFun_apply, Pi.single_apply, zsmul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))

instance instDiscreteIntLat (n : ℕ) : DiscreteTopology (intLat n) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))))

instance instZLatticeIntLat (n : ℕ) : IsZLattice ℝ (intLat n) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))))

/-- **Construction A in `ℝⁿ`**: `Λ(g) = {x ∈ ℤⁿ : x mod p ∈ ⟨g⟩} ⊆ ℝⁿ`. -/
def latR (p n : ℕ) (g : Fin n → ZMod p) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.map (toReal n) (latZ p n g)

theorem latR_le_intLat (g : Fin n → ZMod p) : latR p n g ≤ intLat n := by
  rw [intLat_eq_range]
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

theorem smul_intLat_le_latR (g : Fin n → ZMod p) :
    ∀ x ∈ intLat n, (p : ℤ) • x ∈ latR p n g := by
  rw [intLat_eq_range]
  rintro _ ⟨y, rfl⟩
  exact ⟨(p : ℤ) • y, smul_mem_latZ g y, by rw [map_smul]⟩

instance instDiscreteLatR (g : Fin n → ZMod p) : DiscreteTopology (latR p n g) :=
  discreteTopology_of_le (intLat n) _ (latR_le_intLat g)

instance instZLatticeLatR [NeZero p] (g : Fin n → ZMod p) : IsZLattice ℝ (latR p n g) where
  span_top := span_real_eq_top_of_smul_le (intLat n) (latR p n g)
    (NeZero.ne p) (smul_intLat_le_latR g)

theorem natCard_lineZ [Fact (Nat.Prime p)] (g : Fin n → ZMod p) (hg : g ≠ 0) :
    Nat.card (Submodule.span (ZMod p) ({g} : Set (Fin n → ZMod p))) = p := by
  set_option backward.isDefEq.respectTransparency false in
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), finrank_span_singleton hg,
      pow_one, Nat.card_zmod]

theorem natCard_lineZ' [Fact (Nat.Prime p)] (g : Fin n → ZMod p) (hg : g ≠ 0) :
    Nat.card (lineZ g).toAddSubgroup = p := natCard_lineZ g hg

theorem index_lineZ [Fact (Nat.Prime p)] (hn : 1 ≤ n) (g : Fin n → ZMod p) (hg : g ≠ 0) :
    (lineZ g).toAddSubgroup.index = p ^ (n - 1) := by
  have : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  have hmul := AddSubgroup.card_mul_index (lineZ g).toAddSubgroup
  rw [natCard_lineZ' g hg] at hmul
  have hcard : Nat.card (Fin n → ZMod p) = p ^ n := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hcard] at hmul
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, mul_comm (p ^ m) p] at hmul
  simp only [Nat.add_sub_cancel]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne p)) hmul

/-- **The index of Construction A in `ℤⁿ` is `p^{n-1}`.** -/
theorem index_latZ [Fact (Nat.Prime p)] (hn : 1 ≤ n) (g : Fin n → ZMod p) (hg : g ≠ 0) :
    (latZ p n g).toAddSubgroup.index = p ^ (n - 1) := by
  have : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  rw [← index_lineZ hn g hg]
  exact AddSubgroup.index_comap_of_surjective (lineZ g).toAddSubgroup
    (f := (redLin p n).toAddMonoidHom) redLin_surjective

/-- `toReal` as a `ℤ`-linear equivalence onto the standard integer lattice of `ℝⁿ`. -/
noncomputable def toRealEquiv (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] (intLat n) :=
  (LinearEquiv.ofInjective (toReal n) toReal_injective).trans
    (LinearEquiv.ofEq _ _ (intLat_eq_range n).symm)

theorem toRealEquiv_coe (n : ℕ) (y : Fin n → ℤ) : ((toRealEquiv n y : Fin n → ℝ)) = toReal n y :=
  rfl

theorem toReal_mem_latR_iff (g : Fin n → ZMod p) (y : Fin n → ℤ) :
    toReal n y ∈ latR p n g ↔ y ∈ latZ p n g := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    rwa [toReal_injective hzy] at hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem comap_addSubgroupOf (g : Fin n → ZMod p) :
    AddSubgroup.comap (toRealEquiv n).toAddEquiv.toAddMonoidHom
        ((latR p n g).toAddSubgroup.addSubgroupOf (intLat n).toAddSubgroup)
      = (latZ p n g).toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup]
  exact toReal_mem_latR_iff g y

/-- **The relative index of `Λ(g)` in `ℤⁿ ⊆ ℝⁿ` is `p^{n-1}`.** -/
theorem relIndex_latR [Fact (Nat.Prime p)] (hn : 1 ≤ n) (g : Fin n → ZMod p) (hg : g ≠ 0) :
    (latR p n g).toAddSubgroup.relIndex (intLat n).toAddSubgroup = p ^ (n - 1) := by
  have hsurj : Function.Surjective ⇑(toRealEquiv n).toAddEquiv.toAddMonoidHom :=
    (toRealEquiv n).toAddEquiv.surjective
  rw [AddSubgroup.relIndex,
    ← AddSubgroup.index_comap_of_surjective
        ((latR p n g).toAddSubgroup.addSubgroupOf (intLat n).toAddSubgroup) hsurj,
    comap_addSubgroupOf g, index_latZ hn g hg]

/-- A `ℤ`-basis of the standard integer lattice of `ℝⁿ`. -/
noncomputable def intLatBasis (n : ℕ) : Module.Basis (Fin n) ℤ (intLat n) :=
  (Pi.basisFun ℤ (Fin n)).map (toRealEquiv n)

theorem covolume_intLat (n : ℕ) : ZLattice.covolume (intLat n) = 1 := by
  classical
  rw [ZLattice.covolume_eq_det (intLat n) (intLatBasis n)]
  have : (Matrix.of ((↑) ∘ (intLatBasis n))) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [intLatBasis, toRealEquiv_coe, toReal_apply, Pi.basisFun_apply, Pi.single_apply,
      Matrix.one_apply, eq_comm]
  rw [this, Matrix.det_one, abs_one]

/-- **The covolume of Construction A.** `covol Λ(g) = p^{n-1}`. -/
theorem covolume_latR [Fact (Nat.Prime p)] (hn : 1 ≤ n) (g : Fin n → ZMod p) (hg : g ≠ 0) :
    ZLattice.covolume (latR p n g) = (p : ℝ) ^ (n - 1) := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex (latR p n g) (intLat n)
    (latR_le_intLat g)
  rw [covolume_intLat, div_one, relIndex_latR hn g hg] at h
  rw [h]
  push_cast
  ring

/-- Membership in Construction A is exactly the incidence relation counted above. -/
theorem mem_latZ_iff_onLine (g : Fin n → ZMod p) (y : Fin n → ℤ) :
    y ∈ latZ p n g ↔ OnLine g (redMod p y) := mem_latZ g y

end D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
