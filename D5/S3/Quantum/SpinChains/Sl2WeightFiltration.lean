/- GID: D5/S3/Quantum/SpinChains/Sl2WeightFiltration
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/Sl2WeightFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral sl₂ weights control the ranks of filtration-lowering endomorphisms. -/

import D5.S3.Quantum.SpinChains.HypereclecticNonShortening

attribute [local instance] LieRing.ofAssociativeRing

namespace D5.S3.Quantum.SpinChains.Sl2WeightFiltration

open Module

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- The commutator relations, including the zero representation. -/
structure Sl2Relations (h e f : Module.End K V) : Prop where
  ef : e * f - f * e = h
  he : h * e - e * h = (2 : K) • e
  hf : h * f - f * h = -(2 : K) • f

/-- The weight subspace with integer label. -/
def weightSpace (h : Module.End K V) (s : ℤ) : Submodule K V := h.eigenspace (s : K)

/-- A finite certificate that integer weight subspaces span the representation. -/
def IntegralWeights (h : Module.End K V) : Prop :=
  ∃ S : Finset ℤ, (⨆ s ∈ S, weightSpace h s) = ⊤

/-- The increasing filtration by integer weights. -/
def weightLE (h : Module.End K V) (s : ℤ) : Submodule K V :=
  ⨆ t : ℤ, ⨆ (_ : t ≤ s), weightSpace h t

/-- The decreasing filtration by integer weights. -/
def weightGE (h : Module.End K V) (s : ℤ) : Submodule K V :=
  ⨆ t : ℤ, ⨆ (_ : s ≤ t), weightSpace h t

omit [CharZero K] in
private theorem relations_symm {h e f : Module.End K V} (a : Sl2Relations h e f) :
    Sl2Relations (-h) f e := by
  constructor
  · rw [← a.ef]; abel
  · calc
      (-h) * f - f * (-h) = -(h * f - f * h) := by simp only [neg_mul, mul_neg]; abel
      _ = (2 : K) • f := by rw [a.hf]; simp
  · calc
      (-h) * e - e * (-h) = -(h * e - e * h) := by simp only [neg_mul, mul_neg]; abel
      _ = -(2 : K) • e := by rw [a.he]; simp

private theorem shift_pow {h a : Module.End K V} {δ μ : K}
    (ha : h * a - a * h = δ • a) {v : V} (hv : h v = μ • v) (r : ℕ) :
    h ((a ^ r) v) = (μ + r * δ) • ((a ^ r) v) := by
  induction r with
  | zero => simpa using hv
  | succ r ih =>
    have z := congrArg (fun A : Module.End K V => A ((a ^ r) v)) ha
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at z
    rw [ih, map_smul] at z
    rw [pow_succ', Module.End.mul_apply]
    rw [show h (a ((a ^ r) v)) = δ • a ((a ^ r) v) +
      (μ + r * δ) • a ((a ^ r) v) by exact (sub_eq_iff_eq_add.mp z)]
    simp only [Nat.cast_add, Nat.cast_one]
    module

/-- Raising powers shift the integer weight by twice the exponent. -/
theorem raising_pow_weight {h e f : Module.End K V} (a : Sl2Relations h e f)
    {s : ℤ} {v : V} (hv : v ∈ weightSpace h s) (r : ℕ) :
    (e ^ r) v ∈ weightSpace h (s + 2 * (r : ℤ)) := by
  apply Module.End.mem_eigenspace_iff.mpr
  have z := shift_pow a.he (Module.End.mem_eigenspace_iff.mp hv) r
  convert z using 2
  push_cast
  ring

/-- Lowering powers shift the integer weight by minus twice the exponent. -/
theorem lowering_pow_weight {h e f : Module.End K V} (a : Sl2Relations h e f)
    {s : ℤ} {v : V} (hv : v ∈ weightSpace h s) (r : ℕ) :
    (f ^ r) v ∈ weightSpace h (s - 2 * (r : ℤ)) := by
  apply Module.End.mem_eigenspace_iff.mpr
  have z := shift_pow a.hf (Module.End.mem_eigenspace_iff.mp hv) r
  convert z using 2
  push_cast
  ring

/-- The lowering power as a map into its shifted weight subspace. -/
def loweringMap {h e f : Module.End K V} (a : Sl2Relations h e f) (s : ℤ) (r : ℕ) :
    weightSpace h s →ₗ[K] weightSpace h (s - 2 * (r : ℤ)) :=
  ((f ^ r).comp (weightSpace h s).subtype).codRestrict _
    (fun v => lowering_pow_weight a v.property r)

/-- The raising power as a map into its shifted weight subspace. -/
def raisingMap {h e f : Module.End K V} (a : Sl2Relations h e f) (s : ℤ) (r : ℕ) :
    weightSpace h s →ₗ[K] weightSpace h (s + 2 * (r : ℤ)) :=
  ((e ^ r).comp (weightSpace h s).subtype).codRestrict _
    (fun v => raising_pow_weight a v.property r)

private theorem locally_nilpotent_of_shift [FiniteDimensional K V]
    {h a : Module.End K V} {δ μ : K} (ha : h * a - a * h = δ • a) (hδ : δ ≠ 0)
    {v : V} (hv : h v = μ • v) : ∃ n : ℕ, (a ^ n) v = 0 := by
  by_contra hn
  have hn' : ∀ n : ℕ, (a ^ n) v ≠ 0 := by simpa using hn
  have hi : Function.Injective (fun n : ℕ => μ + n * δ) := by
    intro m n heq
    apply Nat.cast_injective (R := K)
    exact mul_right_cancel₀ hδ (add_left_cancel heq)
  have li := h.eigenvectors_linearIndependent' (fun n : ℕ => μ + n * δ) hi
    (fun n => (a ^ n) v) (fun n => ⟨Module.End.mem_eigenspace_iff.mpr
      (shift_pow ha hv n), hn' n⟩)
  exact Module.Finite.not_linearIndependent_of_infinite _ li

/-- Every weight vector is locally annihilated by the raising operator. -/
theorem raising_locally_nilpotent [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f)
    {s : ℤ} {v : V} (hv : v ∈ weightSpace h s) : ∃ n : ℕ, (e ^ n) v = 0 :=
  locally_nilpotent_of_shift a.he (by norm_num) (Module.End.mem_eigenspace_iff.mp hv)

/-- Every weight vector is locally annihilated by the lowering operator. -/
theorem lowering_locally_nilpotent [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f)
    {s : ℤ} {v : V} (hv : v ∈ weightSpace h s) : ∃ n : ℕ, (f ^ n) v = 0 :=
  locally_nilpotent_of_shift a.hf (by norm_num) (Module.End.mem_eigenspace_iff.mp hv)

private theorem kernel_zero_of_relations {h e f : Module.End K V}
    (a : Sl2Relations h e f) {v : V} {q r n : ℕ}
    (hv : h v = (q : K) • v) (hr : r ≤ q)
    (hn : (e ^ n) v = 0) (hz : (f ^ r) v = 0) : v = 0 := by
  by_cases hh : h = 0
  · by_cases hq : q = 0
    · have : r = 0 := by omega
      simpa [this] using hz
    · have z : (q : K) • v = 0 := by simpa [hh] using hv.symm
      exact (smul_eq_zero.mp z).resolve_left (by exact_mod_cast hq)
  · have triple : IsSl2Triple h e f := {
      h_ne_zero := hh
      lie_e_f := a.ef
      lie_h_e_nsmul := by simpa [Ring.lie_def, two_smul] using a.he
      lie_h_f_nsmul := by simpa [Ring.lie_def, two_smul] using a.hf }
    exact HypereclecticNonShortening.lowering_kernel_zero triple n v q r hv hr hn hz

/-- A lowering power is injective on a weight at least its exponent. -/
theorem lowering_pow_injective [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (s : ℤ) (r : ℕ)
    (hr : (r : ℤ) ≤ s) : Function.Injective (loweringMap a s r) := by
  intro x y eqxy
  have hxy := congrArg Subtype.val eqxy
  have hv : (x : V) - y ∈ weightSpace h s := Submodule.sub_mem _ x.property y.property
  obtain ⟨n, hn⟩ := raising_locally_nilpotent a hv
  have hs : 0 ≤ s := by omega
  have hw : h ((x : V) - y) = (s.toNat : K) • ((x : V) - y) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]
    exact Module.End.mem_eigenspace_iff.mp hv
  have hz : (f ^ r) ((x : V) - y) = 0 := by
    change (f ^ r) (x : V) = (f ^ r) (y : V) at hxy
    rw [map_sub, hxy, sub_self]
  have z := kernel_zero_of_relations a hw (by omega) hn hz
  exact Subtype.ext (sub_eq_zero.mp z)

/-- A raising power is injective on a weight at most minus its exponent. -/
theorem raising_pow_injective [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (t : ℤ) (r : ℕ)
    (hr : t ≤ -(r : ℤ)) : Function.Injective (raisingMap a t r) := by
  intro x y eqxy
  have hxy := congrArg Subtype.val eqxy
  have hv : (x : V) - y ∈ weightSpace h t := Submodule.sub_mem _ x.property y.property
  obtain ⟨n, hn⟩ := lowering_locally_nilpotent a hv
  have ht : 0 ≤ -t := by omega
  have hw : (-h) ((x : V) - y) = ((-t).toNat : K) • ((x : V) - y) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg ht]
    change -(h ((x : V) - y)) = ((-t : ℤ) : K) • ((x : V) - y)
    rw [Module.End.mem_eigenspace_iff.mp hv, Int.cast_neg, neg_smul]
  have hz : (e ^ r) ((x : V) - y) = 0 := by
    change (e ^ r) (x : V) = (e ^ r) (y : V) at hxy
    rw [map_sub, hxy, sub_self]
  have z := kernel_zero_of_relations (relations_symm a) hw (by omega) hn hz
  exact Subtype.ext (sub_eq_zero.mp z)

private theorem lowering_injective_val [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (s : ℤ) (r : ℕ)
    (hr : (r : ℤ) ≤ s) :
    Function.Injective ((f ^ r).comp (weightSpace h s).subtype) :=
  (LinearMap.injective_codRestrict_iff _).mp (lowering_pow_injective a s r hr)

private theorem raising_injective_val [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (t : ℤ) (r : ℕ)
    (hr : t ≤ -(r : ℤ)) :
    Function.Injective ((e ^ r).comp (weightSpace h t).subtype) :=
  (LinearMap.injective_codRestrict_iff _).mp (raising_pow_injective a t r hr)

/-- Opposite integer weight spaces have equal dimension. -/
theorem weight_finrank_symm [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (s : ℤ) :
    finrank K (weightSpace h s) = finrank K (weightSpace h (-s)) := by
  have pos (s : ℤ) (hs : 0 ≤ s) :
      finrank K (weightSpace h s) = finrank K (weightSpace h (-s)) := by
    let L : weightSpace h s →ₗ[K] weightSpace h (-s) :=
      ((f ^ s.toNat).comp (weightSpace h s).subtype).codRestrict _ (fun v => by
        have label : s - 2 * (s.toNat : ℤ) = -s := by omega
        simpa only [label, LinearMap.comp_apply, Submodule.subtype_apply] using
          lowering_pow_weight a v.property s.toNat)
    let R : weightSpace h (-s) →ₗ[K] weightSpace h s :=
      ((e ^ s.toNat).comp (weightSpace h (-s)).subtype).codRestrict _ (fun v => by
        have label : -s + 2 * (s.toNat : ℤ) = s := by omega
        simpa only [label, LinearMap.comp_apply, Submodule.subtype_apply] using
          raising_pow_weight a v.property s.toNat)
    have hL : Function.Injective L := by
      intro x y eq
      exact lowering_injective_val a s s.toNat (by omega)
        (congrArg (fun z : weightSpace h (-s) => (z : V)) eq)
    have hR : Function.Injective R := by
      intro x y eq
      exact raising_injective_val a (-s) s.toNat (by omega)
        (congrArg (fun z : weightSpace h s => (z : V)) eq)
    exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hL)
      (LinearMap.finrank_le_finrank_of_injective hR)
  by_cases hs : 0 ≤ s
  · exact pos s hs
  · have eq := pos (-s) (by omega)
    rw [neg_neg] at eq
    exact eq.symm

/-- Lowering powers reach every vector in a sufficiently negative target weight. -/
theorem lowering_pow_surjective [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (t : ℤ) (r : ℕ)
    (ht : t ≤ -(r : ℤ)) (y : V) (hy : y ∈ weightSpace h t) :
    ∃ x ∈ weightSpace h (t + 2 * (r : ℤ)), (f ^ r) x = y := by
  let n := (-t).toNat
  have hn : (n : ℤ) = -t := Int.toNat_of_nonneg (by omega)
  have hrn : r ≤ n := by omega
  let L : weightSpace h (-t) →ₗ[K] weightSpace h t :=
    ((f ^ n).comp (weightSpace h (-t)).subtype).codRestrict _ (fun v => by
      have label : -t - 2 * (n : ℤ) = t := by omega
      simpa only [label, LinearMap.comp_apply, Submodule.subtype_apply] using
        lowering_pow_weight a v.property n)
  have hL : Function.Injective L := by
    intro x z eq
    exact lowering_injective_val a (-t) n (by omega)
      (congrArg (fun w : weightSpace h t => (w : V)) eq)
  have dim : finrank K (weightSpace h (-t)) = finrank K (weightSpace h t) := by
    have eq := weight_finrank_symm a (-t)
    rw [neg_neg] at eq
    exact eq
  obtain ⟨z, hz⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp hL ⟨y, hy⟩
  refine ⟨(f ^ (n - r)) z, ?_, ?_⟩
  · have label : -t - 2 * ((n - r : ℕ) : ℤ) = t + 2 * (r : ℤ) := by omega
    simpa only [label, LinearMap.comp_apply, Submodule.subtype_apply] using
      lowering_pow_weight a z.property (n - r)
  · have hzy : (f ^ n) (z : V) = y := congrArg Subtype.val hz
    rw [← Module.End.mul_apply, ← pow_add, show r + (n - r) = n by omega, hzy]

private theorem weight_independent (h : Module.End K V) :
    iSupIndep (weightSpace h) :=
  h.eigenspaces_iSupIndep.comp (Int.cast_injective : Function.Injective (fun s : ℤ => (s : K)))

private theorem weight_cuts_disjoint (h : Module.End K V) (c : ℤ) :
    Disjoint (weightGE h c) (weightLE h (c - 1)) := by
  exact (weight_independent h).disjoint_biSup_biSup
    (s := Set.Ici c) (t := Set.Iic (c - 1)) (Set.disjoint_left.mpr (by
      intro s hs ht
      change c ≤ s at hs
      change s ≤ c - 1 at ht
      omega))

omit [CharZero K] in
private theorem weight_cuts_sup {h : Module.End K V} (hw : IntegralWeights h) (c : ℤ) :
    weightGE h c ⊔ weightLE h (c - 1) = ⊤ := by
  obtain ⟨S, hS⟩ := hw
  apply top_unique
  rw [← hS]
  refine iSup₂_le fun s _ => ?_
  by_cases hs : c ≤ s
  · exact le_sup_of_le_left (le_iSup_of_le s (le_iSup_of_le hs le_rfl))
  · exact le_sup_of_le_right (le_iSup_of_le s (le_iSup_of_le (by omega) le_rfl))

private theorem lowering_map_LE {h e f : Module.End K V} (a : Sl2Relations h e f)
    (s : ℤ) (r : ℕ) :
    (weightLE h s).map (f ^ r) ≤ weightLE h (s - 2 * (r : ℤ)) := by
  simp only [weightLE, Submodule.map_iSup]
  refine iSup₂_le fun t ht => ?_
  rintro _ ⟨v, hv, rfl⟩
  exact Submodule.mem_iSup_of_mem (t - 2 * (r : ℤ))
    (Submodule.mem_iSup_of_mem (show t - 2 * (r : ℤ) ≤ s - 2 * (r : ℤ) by omega)
      (lowering_pow_weight a hv r))

private theorem lowering_map_GE {h e f : Module.End K V} (a : Sl2Relations h e f)
    (s : ℤ) (r : ℕ) :
    (weightGE h s).map (f ^ r) ≤ weightGE h (s - 2 * (r : ℤ)) := by
  simp only [weightGE, Submodule.map_iSup]
  refine iSup₂_le fun t ht => ?_
  rintro _ ⟨v, hv, rfl⟩
  exact Submodule.mem_iSup_of_mem (t - 2 * (r : ℤ))
    (Submodule.mem_iSup_of_mem (show s - 2 * (r : ℤ) ≤ t - 2 * (r : ℤ) by omega)
      (lowering_pow_weight a hv r))

private theorem lowering_map_low_eq [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (r : ℕ) :
    (weightLE h ((r : ℤ) - 1)).map (f ^ r) = weightLE h (-(r : ℤ) - 1) := by
  apply le_antisymm
  · have z := lowering_map_LE a ((r : ℤ) - 1) r
    have label : (r : ℤ) - 1 - 2 * (r : ℤ) = -(r : ℤ) - 1 := by omega
    simpa only [label] using z
  · refine iSup₂_le fun t ht => ?_
    intro y hy
    obtain ⟨x, hx, hxy⟩ := lowering_pow_surjective a t r (by omega) y hy
    exact Submodule.mem_map.mpr ⟨x,
      Submodule.mem_iSup_of_mem (t + 2 * (r : ℤ))
        (Submodule.mem_iSup_of_mem (show t + 2 * (r : ℤ) ≤ (r : ℤ) - 1 by omega) hx),
      hxy⟩

private theorem lowering_kernel_GE [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (r : ℕ)
    {x : V} (hx : x ∈ weightGE h (r : ℤ)) (hz : (f ^ r) x = 0) : x = 0 := by
  classical
  let I := {s : ℤ // (r : ℤ) ≤ s}
  have hx' : x ∈ ⨆ i : I, weightSpace h i.val := by
    simpa only [weightGE, iSup_subtype'] using hx
  obtain ⟨v, hv, hvx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp hx'
  have hi : iSupIndep (fun i : I => weightSpace h (i.val - 2 * (r : ℤ))) := by
    apply h.eigenspaces_iSupIndep.comp
    intro i j eq
    apply Subtype.ext
    have z : i.val - 2 * (r : ℤ) = j.val - 2 * (r : ℤ) := Int.cast_injective eq
    omega
  have hsum : ∑ i ∈ v.support, (f ^ r) (v i) = 0 := by
    have z := congrArg (fun x : V => (f ^ r) x) hvx
    simpa only [Finsupp.sum, map_sum, hz] using z
  have hcomp := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hi v.support
    (fun i => (f ^ r) (v i)) (fun i _ => lowering_pow_weight a (hv i) r) hsum
  rw [← hvx]
  apply Finset.sum_eq_zero
  intro i hi
  have inj := lowering_injective_val a i.val r i.property
  have z := @inj ⟨v i, hv i⟩ 0 (by
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, map_zero] using hcomp i hi)
  exact congrArg (fun y : weightSpace h i.val => (y : V)) z

/-- The rank of a lowering power is the sum of two complementary weight tails. -/
theorem lowering_rank_formula [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (hw : IntegralWeights h) (r : ℕ) :
    finrank K (LinearMap.range (f ^ r)) =
      finrank K (weightGE h (r : ℤ)) + finrank K (weightLE h (-(r : ℤ) - 1)) := by
  let A := weightGE h (r : ℤ)
  let B := weightLE h ((r : ℤ) - 1)
  let C := weightLE h (-(r : ℤ) - 1)
  have hAB : A ⊔ B = ⊤ := weight_cuts_sup hw (r : ℤ)
  have hBC : B.map (f ^ r) = C := lowering_map_low_eq a r
  have hAC : Disjoint (A.map (f ^ r)) C := by
    have hg : A.map (f ^ r) ≤ weightGE h (-(r : ℤ)) := by
      have z := lowering_map_GE a (r : ℤ) r
      have label : (r : ℤ) - 2 * (r : ℤ) = -(r : ℤ) := by omega
      simpa only [label] using z
    exact (weight_cuts_disjoint h (-(r : ℤ))).mono_left hg
  have hrange : LinearMap.range (f ^ r) = A.map (f ^ r) ⊔ C := by
    rw [LinearMap.range_eq_map, ← hAB, Submodule.map_sup, hBC]
  have hA : finrank K (A.map (f ^ r)) = finrank K A := by
    let L := (f ^ r).domRestrict A
    have inj : Function.Injective L := by
      intro x y eq
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply lowering_kernel_GE a r (Submodule.sub_mem _ x.property y.property)
      change (f ^ r) (x : V) = (f ^ r) (y : V) at eq
      rw [map_sub, eq, sub_self]
    have z := (LinearEquiv.ofInjective L inj).finrank_eq
    rw [LinearMap.range_domRestrict] at z
    exact z.symm
  have z := Submodule.finrank_sup_add_finrank_inf_eq (A.map (f ^ r)) C
  rw [hAC.eq_bot, finrank_bot, add_zero, ← hrange, hA] at z
  exact z

omit [CharZero K] in
/-- Iterating a filtration-lowering endomorphism lowers by twice the exponent. -/
theorem filtration_pow_map_le (F : ℤ → Submodule K V) (T : Module.End K V)
    (hT : ∀ s : ℤ, (F s).map T ≤ F (s - 2)) (s : ℤ) (r : ℕ) :
    (F s).map (T ^ r) ≤ F (s - 2 * (r : ℤ)) := by
  induction r generalizing s with
  | zero => simp only [pow_zero, Module.End.one_eq_id, Submodule.map_id,
      Nat.cast_zero, mul_zero, sub_zero, le_refl]
  | succ r ih =>
    rw [pow_succ', Module.End.mul_eq_comp, Submodule.map_comp]
    have z := (Submodule.map_mono (ih s)).trans (hT (s - 2 * (r : ℤ)))
    have label : s - 2 * (r : ℤ) - 2 = s - 2 * ((r + 1 : ℕ) : ℤ) := by omega
    simpa only [label] using z

omit [CharZero K] in
private theorem filtration_kernel_bound [FiniteDimensional K V]
    (F : ℤ → Submodule K V) (T : Module.End K V)
    (hT : ∀ s : ℤ, (F s).map T ≤ F (s - 2)) (r : ℕ) :
    finrank K (F ((r : ℤ) - 1)) ≤
      finrank K (LinearMap.ker (T ^ r)) + finrank K (F (-(r : ℤ) - 1)) := by
  let B := F ((r : ℤ) - 1)
  let C := F (-(r : ℤ) - 1)
  let L := (T ^ r).domRestrict B
  have image : LinearMap.range L ≤ C := by
    rw [LinearMap.range_domRestrict]
    have z := filtration_pow_map_le F T hT ((r : ℤ) - 1) r
    have label : (r : ℤ) - 1 - 2 * (r : ℤ) = -(r : ℤ) - 1 := by omega
    simpa only [label] using z
  have kernel : finrank K (LinearMap.ker L) ≤ finrank K (LinearMap.ker (T ^ r)) := by
    have eqmap : (LinearMap.ker L).map B.subtype = B ⊓ LinearMap.ker (T ^ r) := by
      rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
    have z := Submodule.finrank_mono
      (inf_le_right : B ⊓ LinearMap.ker (T ^ r) ≤ LinearMap.ker (T ^ r))
    rw [← eqmap, Submodule.finrank_map_subtype_eq] at z
    exact z
  have range := Submodule.finrank_mono image
  have dims := L.finrank_range_add_finrank_ker
  change finrank K B ≤ finrank K (LinearMap.ker (T ^ r)) + finrank K C
  omega

/-- Among endomorphisms lowering the integral weight filtration by two, the sl₂ lowering
operator has maximal rank at every natural power. -/
theorem rank_comparison [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (hw : IntegralWeights h)
    (T : Module.End K V) (hT : ∀ s : ℤ, (weightLE h s).map T ≤ weightLE h (s - 2))
    (r : ℕ) : finrank K (LinearMap.range (T ^ r)) ≤ finrank K (LinearMap.range (f ^ r)) := by
  have bound := filtration_kernel_bound (weightLE h) T hT r
  have rank := lowering_rank_formula a hw r
  have split := Submodule.finrank_sup_add_finrank_inf_eq
    (weightGE h (r : ℤ)) (weightLE h ((r : ℤ) - 1))
  rw [(weight_cuts_disjoint h (r : ℤ)).eq_bot, finrank_bot, add_zero,
    weight_cuts_sup hw (r : ℤ), finrank_top] at split
  have nullity := (T ^ r).finrank_range_add_finrank_ker
  omega

/-- On every eigenspace of a commuting operator, the sl₂ lowering operator has
maximal power ranks among operators lowering the integral weight filtration by two. -/
theorem eigenspace_rank_comparison [FiniteDimensional K V]
    {h e f U : Module.End K V} (a : Sl2Relations h e f) (hw : IntegralWeights h)
    (T : Module.End K V) (hT : ∀ s : ℤ, (weightLE h s).map T ≤ weightLE h (s - 2))
    (hUh : Commute U h) (hUe : Commute U e) (hUf : Commute U f) (hUT : Commute U T)
    (μ : K) (r : ℕ) :
    finrank K (LinearMap.range
      ((T.restrict (Module.End.mapsTo_genEigenspace_of_comm hUT μ 1)) ^ r)) ≤
    finrank K (LinearMap.range
      ((f.restrict (Module.End.mapsTo_genEigenspace_of_comm hUf μ 1)) ^ r)) := by
  classical
  let W := U.eigenspace μ
  have invariant (A : Module.End K V) (hUA : Commute U A) :
      ∀ v ∈ W, A v ∈ W := Module.End.mapsTo_genEigenspace_of_comm hUA μ 1
  let H := h.restrict (invariant h hUh)
  let E := e.restrict (invariant e hUe)
  let F := f.restrict (invariant f hUf)
  let L := T.restrict (invariant T hUT)
  have relations : Sl2Relations H E F := by
    constructor
    · ext v
      exact congrArg (fun A : Module.End K V => A (v : V)) a.ef
    · ext v
      exact congrArg (fun A : Module.End K V => A (v : V)) a.he
    · ext v
      exact congrArg (fun A : Module.End K V => A (v : V)) a.hf
  have weight_eq (s : ℤ) : weightSpace H s = (weightSpace h s).comap W.subtype :=
    h.genEigenspace_restrict W 1 (s : K) (invariant h hUh)
  -- Independence forces every weight component of an eigenvector of U to have
  -- the same eigenvalue of U. The argument also applies to any selected weights.
  have selected_weights (P : ℤ → Prop) :
      (⨆ s, ⨆ (_ : P s), weightSpace H s) =
        (⨆ s, ⨆ (_ : P s), weightSpace h s).comap W.subtype := by
    apply le_antisymm
    · refine iSup₂_le fun s hs => ?_
      rw [weight_eq]
      exact Submodule.comap_mono (le_iSup_of_le s (le_iSup_of_le hs le_rfl))
    · intro v hv
      obtain ⟨x, hx, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp
        (fun s => ⨆ (_ : P s), weightSpace h s) (v : V)).mp hv
      have hxweight (s : ℤ) : x s ∈ weightSpace h s :=
        (show (⨆ (_ : P s), weightSpace h s) ≤ weightSpace h s from
          iSup_le fun _ => le_rfl) (hx s)
      have defect_weight (s : ℤ) : U (x s) - μ • x s ∈ weightSpace h s :=
        (weightSpace h s).sub_mem
          (Module.End.mapsTo_genEigenspace_of_comm hUh.symm (s : K) 1 (hxweight s))
          ((weightSpace h s).smul_mem μ (hxweight s))
      have defect_sum : ∑ s ∈ x.support, (U (x s) - μ • x s) = 0 := by
        rw [Finset.sum_sub_distrib, ← map_sum, ← Finset.smul_sum]
        change U (x.sum fun _ z => z) - μ • (x.sum fun _ z => z) = 0
        rw [hsum, Module.End.mem_eigenspace_iff.mp v.property, sub_self]
      have defect_zero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
        (weightSpace h)).mp (weight_independent h) x.support
        (fun s => U (x s) - μ • x s) (fun s _ => defect_weight s) defect_sum
      have hxW (s : ℤ) : x s ∈ W := by
        by_cases hs : s ∈ x.support
        · exact Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp (defect_zero s hs))
        · simp only [Finsupp.notMem_support_iff.mp hs, Submodule.zero_mem]
      let y : ℤ → W := fun s => ⟨x s, hxW s⟩
      have hy (s : ℤ) : y s ∈ ⨆ (_ : P s), weightSpace H s := by
        by_cases hs : P s
        · apply Submodule.mem_iSup_of_mem hs
          rw [weight_eq]
          exact hxweight s
        · have hz : x s = 0 := by simpa [hs] using hx s
          have hyz : y s = 0 := Subtype.ext hz
          rw [hyz]
          exact Submodule.zero_mem _
      have sum_y : ∑ s ∈ x.support, y s = v := by
        apply Subtype.ext
        change W.subtype (∑ s ∈ x.support, y s) = (v : V)
        rw [map_sum]
        exact hsum
      rw [← sum_y]
      exact Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s (hy s)
  have integral : IntegralWeights H := by
    obtain ⟨S, hS⟩ := hw
    refine ⟨S, ?_⟩
    rw [selected_weights (fun s => s ∈ S), hS, Submodule.comap_top]
  have filtration (s : ℤ) : weightLE H s = (weightLE h s).comap W.subtype :=
    selected_weights (fun t => t ≤ s)
  have lowers (s : ℤ) : (weightLE H s).map L ≤ weightLE H (s - 2) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [filtration] at hv ⊢
    exact hT s (Submodule.mem_map_of_mem hv)
  exact rank_comparison relations integral L lowers r

end D5.S3.Quantum.SpinChains.Sl2WeightFiltration
