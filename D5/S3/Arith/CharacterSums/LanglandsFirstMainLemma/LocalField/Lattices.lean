/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Lattices
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream valuation-lattice support required by the retained local-field closure. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/LocalField/Lattices.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField.Valuation

/-!
# Integer-indexed fractional valuation lattices

For a nonarchimedean local field `F`, `lattice F n` is the `𝒪_F`-submodule of `F`
consisting of the elements of normalized order at least `n`.  The scalar ring is Mathlib's
canonical valuation subring; the definition does not introduce another valuation.

The index is an integer.  This is essential for the inverse differents and additive-conductor
lattices in the manuscript.  Besides the elementary membership API, this file proves exact
containment, product and principal-scaling formulas and supplies honest submodule quotients for
congruence classes.
-/

namespace LanglandsFirstMainLemma

open scoped Pointwise
open Filter Topology

section Lattices

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem one_le_iff_pos (x : WithTop ℤ) :
    ((1 : ℤ) : WithTop ℤ) ≤ x ↔ ((0 : ℤ) : WithTop ℤ) < x := by
  by_cases hx : x = ⊤
  · simp [hx]
  · obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
    simp only [WithTop.coe_le_coe, WithTop.coe_lt_coe]
    omega

private theorem coe_add_le_iff_le_sub (r n : ℤ) (x : WithTop ℤ) :
    (((r + n : ℤ) : WithTop ℤ) ≤ x) ↔
      (n : WithTop ℤ) ≤ x - (r : WithTop ℤ) := by
  by_cases hx : x = ⊤
  · simp [hx]
  · obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    simp only [WithTop.coe_le_coe]
    omega

private theorem coe_sub_le_iff_le_add (m n : ℤ) (x : WithTop ℤ) :
    (((m - n : ℤ) : WithTop ℤ) ≤ x) ↔
      (m : WithTop ℤ) ≤ x + (n : WithTop ℤ) := by
  by_cases hx : x = ⊤
  · simp [hx]
  · obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
    simp only [WithTop.coe_le_coe, ← WithTop.coe_add]
    omega

private theorem zsmul_one_withTop (n : ℤ) :
    n • (1 : WithTop ℤ) = (n : WithTop ℤ) := by
  cases n with
  | ofNat n => simp
  | negSucc n =>
      rw [negSucc_zsmul]
      have h : (n + 1) • (1 : WithTop ℤ) =
          (((n + 1) • (1 : ℤ) : ℤ) : WithTop ℤ) :=
        (WithTop.coe_nsmul (1 : ℤ) (n + 1)).symm
      rw [h, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      congr
      rw [Int.negSucc_eq]
      simp

/-- Mathlib's canonical valuation subring, used as the scalar ring of every fractional
valuation lattice. -/
noncomputable abbrev ringOfIntegers : Subring F :=
  (ValuativeRel.valuation F).integer

/-- The integer-indexed fractional valuation lattice
`𝔭_F^n = {x : F | n ≤ ord_F(x)}`, represented as an `𝒪_F`-submodule of `F`. -/
noncomputable def lattice (n : ℤ) : Submodule (ringOfIntegers F) F where
  carrier := {x | (n : WithTop ℤ) ≤ ord F x}
  zero_mem' := by simp
  add_mem' {x y} hx hy := (ord F).map_le_add hx hy
  smul_mem' a x hx := by
    change (n : WithTop ℤ) ≤ ord F ((a : F) * x)
    rw [ord_mul]
    have ha : 0 ≤ ord F (a : F) :=
      (ord_nonneg_iff_mem_integer F a).2 a.property
    simpa only [zero_add] using add_le_add ha hx

@[simp]
theorem mem_lattice {n : ℤ} {x : F} :
    x ∈ lattice F n ↔ (n : WithTop ℤ) ≤ ord F x :=
  Iff.rfl

/-- The zeroth lattice is exactly the underlying set of Mathlib's canonical valuation ring. -/
theorem mem_lattice_zero_iff {x : F} :
    x ∈ lattice F 0 ↔ x ∈ ringOfIntegers F :=
  ord_nonneg_iff_mem_integer F x

/-- As a submodule of `F`, the canonical valuation ring is the multiplicative unit submodule. -/
@[simp]
theorem lattice_zero :
    lattice F 0 = (1 : Submodule (ringOfIntegers F) F) := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_one]
    exact ⟨⟨x, (mem_lattice_zero_iff F).1 hx⟩, rfl⟩
  · rw [Submodule.mem_one]
    rintro ⟨x, rfl⟩
    exact (mem_lattice_zero_iff F).2 x.property

/-- The first lattice, restricted to the valuation ring, is its maximal ideal. -/
theorem mem_lattice_one_iff_mem_maximalIdeal (x : ringOfIntegers F) :
    (x : F) ∈ lattice F 1 ↔
      x ∈ IsLocalRing.maximalIdeal (ringOfIntegers F) := by
  change (((1 : ℤ) : WithTop ℤ) ≤ ord F (x : F)) ↔ _
  rw [one_le_iff_pos]
  exact ord_pos_iff_mem_maximalIdeal F x

/-- Increasing the integer depth decreases the lattice. -/
theorem lattice_antitone {m n : ℤ} (h : m ≤ n) :
    lattice F n ≤ lattice F m := by
  intro x hx
  exact (WithTop.coe_le_coe.mpr h).trans hx

/-- Containment of valuation lattices is exactly reverse comparison of their depths. -/
@[simp]
theorem lattice_le_lattice_iff {m n : ℤ} :
    lattice F n ≤ lattice F m ↔ m ≤ n := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_ord_eq F n
    have hxn : x ∈ lattice F n := by simp [hx]
    have hxm := h hxn
    simpa [hx] using hxm
  · exact lattice_antitone F

/-- Distinct integer depths define distinct fractional lattices. -/
theorem lattice_injective : Function.Injective (lattice F) := by
  intro m n h
  apply le_antisymm
  · exact (lattice_le_lattice_iff F).mp h.ge
  · exact (lattice_le_lattice_iff F).mp h.le

@[simp]
theorem lattice_eq_lattice_iff {m n : ℤ} :
    lattice F m = lattice F n ↔ m = n := by
  constructor
  · intro h
    exact lattice_injective F h
  · rintro rfl
    rfl

@[simp]
theorem lattice_lt_lattice_iff {m n : ℤ} :
    lattice F n < lattice F m ↔ m < n := by
  constructor
  · intro h
    exact lt_of_le_of_ne ((lattice_le_lattice_iff F).mp h.le) fun hmn ↦
      h.ne ((lattice_eq_lattice_iff F).2 hmn.symm)
  · intro h
    exact (lattice_antitone F h.le).lt_of_ne fun hEq ↦
      h.ne ((lattice_eq_lattice_iff F).1 hEq.symm)

/-! ## Topology -/

/-- Every integer-indexed valuation lattice is open. -/
theorem lattice_isOpen (n : ℤ) :
    IsOpen (lattice F n : Set F) := by
  obtain ⟨a, ha⟩ := exists_ord_eq F n
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hopen := (ValuativeRel.valuation F).isOpen_closedBall
    (r := (ValuativeRel.valuation F).restrict a) (by simp [ha0])
  convert hopen using 1
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_lattice]
  rw [← ha, ord_le_ord_iff F a x,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F),
    (ValuativeRel.valuation F).restrict_le_iff]

/-- The integer-indexed valuation lattices form a neighborhood basis of zero. -/
theorem lattice_nhds_zero_hasBasis :
    (nhds (0 : F)).HasBasis (fun _ : ℤ ↦ True) fun n ↦
      (lattice F n : Set F) := by
  rw [Filter.hasBasis_iff]
  intro s
  constructor
  · intro hs
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
    obtain ⟨a, ha⟩ :=
      ValuativeRel.valuation_surjective (γ : ValuativeRel.ValueGroupWithZero F)
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact Units.ne_zero γ ha.symm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 ha0)
    refine ⟨k + 1, trivial, fun x hx ↦ hγ ?_⟩
    change ValuativeRel.valuation F x < (γ : ValuativeRel.ValueGroupWithZero F)
    rw [← ha]
    have hax : ord F a < ord F x := by
      rw [← hk]
      exact (WithTop.coe_lt_coe.mpr (show k < k + 1 by omega)).trans_le hx
    have hv : x <ᵥ a := (ord_lt_ord_iff F a x).1 hax
    rw [lt_iff_not_ge, ← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation F)]
    exact hv
  · rintro ⟨n, -, hns⟩
    exact Filter.mem_of_superset ((lattice_isOpen F n).mem_nhds (by simp)) hns

/-- Every neighborhood of zero contains an integer-indexed valuation lattice. -/
theorem exists_lattice_subset_of_mem_nhds_zero {s : Set F}
    (hs : s ∈ nhds (0 : F)) :
    ∃ n : ℤ, (lattice F n : Set F) ⊆ s := by
  simpa using (lattice_nhds_zero_hasBasis F).mem_iff.mp hs

/-- Every neighborhood of zero contains all sufficiently deep valuation lattices. -/
theorem eventually_lattice_subset_of_mem_nhds_zero {s : Set F}
    (hs : s ∈ nhds (0 : F)) :
    ∀ᶠ n : ℤ in atTop, (lattice F n : Set F) ⊆ s := by
  obtain ⟨m, hm⟩ := exists_lattice_subset_of_mem_nhds_zero F hs
  filter_upwards [eventually_ge_atTop m] with n hn
  intro x hx
  exact hm (lattice_antitone F hn hx)

/-- A family eventually lying in lattices whose integer depths tend to infinity converges to
zero. -/
theorem tendsto_zero_of_eventually_mem_lattice
    {ι : Type*} {l : Filter ι} {d : ι → ℤ} {x : ι → F}
    (hd : Tendsto d l atTop)
    (hx : ∀ᶠ i in l, x i ∈ lattice F (d i)) :
    Tendsto x l (nhds 0) := by
  rw [(lattice_nhds_zero_hasBasis F).tendsto_right_iff]
  intro n _
  filter_upwards [hd.eventually (eventually_ge_atTop n), hx] with i hi hxi
  exact lattice_antitone F hi hxi

/-- The exact `n`-th valuation shell is `lattice n \ lattice (n + 1)`. -/
theorem mem_lattice_and_not_mem_succ_iff {n : ℤ} {x : F} :
    x ∈ lattice F n ∧ x ∉ lattice F (n + 1) ↔
      ord F x = (n : WithTop ℤ) := by
  rw [mem_lattice, mem_lattice]
  constructor
  · rintro ⟨hn, hns⟩
    have hlt : ord F x < ((n + 1 : ℤ) : WithTop ℤ) := lt_of_not_ge hns
    have htop : ord F x ≠ ⊤ := by
      intro h
      simp [h] at hlt
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hk] at hn hlt ⊢
    simp only [WithTop.coe_le_coe, WithTop.coe_lt_coe, WithTop.coe_eq_coe] at hn hlt ⊢
    omega
  · intro h
    constructor
    · simp [h]
    · rw [h, WithTop.coe_le_coe]
      omega

/-- Every fractional lattice contains a nonzero element of its exact integer depth. -/
theorem exists_ne_zero_mem_lattice (n : ℤ) :
    ∃ x : F, x ≠ 0 ∧ x ∈ lattice F n := by
  obtain ⟨x, hx⟩ := exists_ord_eq F n
  refine ⟨x, ?_, by simp [hx]⟩
  intro h
  simp [h] at hx

/-- No fractional valuation lattice is the zero submodule. -/
theorem lattice_ne_bot (n : ℤ) : lattice F n ≠ ⊥ := by
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice F n
  intro h
  have : x = 0 := by simpa [h] using hx
  exact hx0 this

/-- Lattice membership is closed under addition. -/
theorem add_mem_lattice {n : ℤ} {x y : F}
    (hx : x ∈ lattice F n) (hy : y ∈ lattice F n) :
    x + y ∈ lattice F n :=
  (lattice F n).add_mem hx hy

/-- Lattice membership is closed under negation. -/
theorem neg_mem_lattice {n : ℤ} {x : F} (hx : x ∈ lattice F n) :
    -x ∈ lattice F n :=
  (lattice F n).neg_mem hx

/-- Lattice membership is closed under subtraction. -/
theorem sub_mem_lattice {n : ℤ} {x y : F}
    (hx : x ∈ lattice F n) (hy : y ∈ lattice F n) :
    x - y ∈ lattice F n :=
  (lattice F n).sub_mem hx hy

/-- A finite sum of elements of one lattice remains in that lattice. -/
theorem sum_mem_lattice {ι : Type*} {s : Finset ι} {f : ι → F} {n : ℤ}
    (hf : ∀ i ∈ s, f i ∈ lattice F n) :
    ∑ i ∈ s, f i ∈ lattice F n :=
  (lattice F n).sum_mem hf

/-- Orders, and hence lattice depths, add under multiplication. -/
theorem mul_mem_lattice {m n : ℤ} {x y : F}
    (hx : x ∈ lattice F m) (hy : y ∈ lattice F n) :
    x * y ∈ lattice F (m + n) := by
  rw [mem_lattice] at hx hy ⊢
  rw [ord_mul]
  exact add_le_add hx hy

/-- The submodule product is contained in the lattice at the sum of the depths. -/
theorem lattice_mul_le (m n : ℤ) :
    lattice F m * lattice F n ≤ lattice F (m + n) := by
  rw [Submodule.mul_le]
  intro x hx y hy
  exact mul_mem_lattice F hx hy

/-- Every element at depth `m + n` is in the submodule product of the depth-`m` and depth-`n`
lattices.  The proof factors through an element of exact order `m`. -/
theorem lattice_le_mul (m n : ℤ) :
    lattice F (m + n) ≤ lattice F m * lattice F n := by
  intro x hx
  obtain ⟨a, ha⟩ := exists_ord_eq F m
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hma : a ∈ lattice F m := by
    rw [mem_lattice, ha]
  have hnx : a⁻¹ * x ∈ lattice F n := by
    rw [mem_lattice, ord_mul, ord_inv, ha]
    rw [mem_lattice] at hx
    norm_num at hx ⊢
    have h := add_le_add_left hx (-(m : WithTop ℤ))
    simpa [add_assoc, add_comm, add_left_comm] using h
  have hprod := Submodule.mul_mem_mul hma hnx
  simpa [mul_assoc, ha0] using hprod

/-- Fractional valuation lattices multiply by adding their integer depths. -/
@[simp]
theorem lattice_mul (m n : ℤ) :
    lattice F m * lattice F n = lattice F (m + n) :=
  le_antisymm (lattice_mul_le F m n) (lattice_le_mul F m n)

/-- A lower bound on the order of a scalar gives the corresponding inclusion after scaling. -/
theorem lattice_smul_le (a : F) (r n : ℤ)
    (ha : (r : WithTop ℤ) ≤ ord F a) :
    a • lattice F n ≤ lattice F (r + n) := by
  intro x hx
  rw [Submodule.mem_smul_pointwise_iff_exists] at hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [mem_lattice] at hy ⊢
  rw [smul_eq_mul, ord_mul]
  exact add_le_add ha hy

/-- Scaling by an element of exact finite order translates the lattice depth exactly. -/
theorem lattice_smul_of_ord_eq (a : F) (r n : ℤ)
    (ha : ord F a = (r : WithTop ℤ)) :
    a • lattice F n = lattice F (r + n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  ext x
  rw [Submodule.mem_smul_iff_inv_mul_mem ha0, mem_lattice, mem_lattice,
    ord_mul, ord_inv, ha]
  norm_num
  constructor <;> intro h
  · have h' := add_le_add_left h (r : WithTop ℤ)
    simpa [add_assoc, add_comm, add_left_comm] using h'
  · have h' := add_le_add_left h (-(r : WithTop ℤ))
    simpa [add_assoc, add_comm, add_left_comm] using h'

/-- Principal form of a lattice: an element of order `r` carries `𝒪_F` onto `𝔭_F^r`. -/
theorem lattice_smul_zero_of_ord_eq (a : F) (r : ℤ)
    (ha : ord F a = (r : WithTop ℤ)) :
    a • lattice F 0 = lattice F r := by
  simpa using lattice_smul_of_ord_eq F a r 0 ha

/-- Principal equality with the integral lattice characterizes the exact order of its scalar. -/
theorem smul_lattice_zero_eq_iff_ord_eq (a : F) (r : ℤ) :
    a • lattice F 0 = lattice F r ↔ ord F a = (r : WithTop ℤ) := by
  constructor
  · intro h
    have ha0 : a ≠ 0 := by
      intro ha
      subst a
      have hbot : (⊥ : Submodule (ringOfIntegers F) F) = lattice F r := by
        simpa using h
      exact lattice_ne_bot F r hbot.symm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 ha0)
    have hscale := lattice_smul_zero_of_ord_eq F a k hk.symm
    have hkr : lattice F k = lattice F r := hscale.symm.trans h
    exact hk.symm.trans (congrArg ((↑) : ℤ → WithTop ℤ)
      ((lattice_eq_lattice_iff F).1 hkr))
  · exact lattice_smul_zero_of_ord_eq F a r

/-- Scaling by the inverse of an element of order `r` lowers depth by `r`. -/
theorem lattice_inv_smul_of_ord_eq (a : F) (r n : ℤ)
    (ha : ord F a = (r : WithTop ℤ)) :
    a⁻¹ • lattice F n = lattice F (n - r) := by
  have hi : ord F a⁻¹ = ((-r : ℤ) : WithTop ℤ) := by
    rw [ord_inv, ha]
    norm_num
  simpa [sub_eq_add_neg, add_comm] using
    lattice_smul_of_ord_eq F a⁻¹ (-r) n hi

/-- Division by an element of exact order `r` lowers the membership threshold by `r`. -/
theorem div_mem_lattice_iff (a x : F) (r n : ℤ)
    (ha : ord F a = (r : WithTop ℤ)) :
    x / a ∈ lattice F n ↔ x ∈ lattice F (r + n) := by
  rw [mem_lattice, mem_lattice, ord_div, ha]
  exact (coe_add_le_iff_le_sub r n (ord F x)).symm

/-- The submodule ideal quotient (colon) of two fractional lattices subtracts depths. -/
@[simp]
theorem lattice_div (m n : ℤ) :
    lattice F m / lattice F n = lattice F (m - n) := by
  ext x
  rw [Submodule.mem_div_iff_forall_mul_mem, mem_lattice]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := exists_ord_eq F n
    have hyn : y ∈ lattice F n := by simp [hy]
    have hxy := hx y hyn
    rw [mem_lattice, ord_mul, hy] at hxy
    exact (coe_sub_le_iff_le_add m n (ord F x)).2
      (by simpa [add_comm] using hxy)
  · intro hx y hy
    rw [mem_lattice] at hy ⊢
    rw [ord_mul]
    have hxm : (m : WithTop ℤ) ≤ ord F x + (n : WithTop ℤ) :=
      (coe_sub_le_iff_le_add m n (ord F x)).1 hx
    exact hxm.trans (by simpa [add_comm] using add_le_add_left hy (ord F x))

/-- Elementwise form of the exact lattice ideal-quotient calculation. -/
theorem mul_lattice_subset_iff {c : F} {m n : ℤ} :
    (∀ x : F, x ∈ lattice F n → c * x ∈ lattice F m) ↔
      c ∈ lattice F (m - n) := by
  rw [← Submodule.mem_div_iff_forall_mul_mem, lattice_div]

/-- Integer powers of a uniformizer give all fractional valuation lattices. -/
theorem lattice_eq_uniformizer_zpow_smul {π : F}
    (hπ : (ValuativeRel.valuation F).IsUniformizer π) (n : ℤ) :
    lattice F n = π ^ n • lattice F 0 := by
  symm
  apply lattice_smul_zero_of_ord_eq F (π ^ n) n
  rw [ord_zpow, ord_uniformizer F hπ]
  exact zsmul_one_withTop n

/-- Depth congruence is congruence modulo the corresponding fractional lattice. -/
theorem congruentAtDepth_iff_sub_mem_lattice (n : ℤ) (x y : F) :
    CongruentAtDepth n x y ↔ x - y ∈ lattice F n :=
  Iff.rfl

end Lattices

section Quotients

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- For `h : m ≤ n`, the copy of `lattice F n` inside `lattice F m`.  The inclusion proof is
part of the construction, so this is the genuine denominator rather than an unconditional
intersection. -/
noncomputable def latticeInside {m n : ℤ} (h : m ≤ n) :
    Submodule (ringOfIntegers F) (lattice F m) :=
  LinearMap.range (Submodule.inclusion (lattice_antitone F h))

@[simp]
theorem mem_latticeInside {m n : ℤ} (h : m ≤ n) {x : lattice F m} :
    x ∈ latticeInside F h ↔ (x : F) ∈ lattice F n := by
  constructor
  · rintro ⟨y, hy⟩
    rw [← congrArg Subtype.val hy]
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Mapping the internal denominator back to `F` gives exactly the stated deeper lattice. -/
@[simp]
theorem map_latticeInside_subtype {m n : ℤ} (h : m ≤ n) :
    (latticeInside F h).map (lattice F m).subtype = lattice F n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_latticeInside F h).1 hy
  · intro hx
    let y : lattice F m := ⟨x, lattice_antitone F h hx⟩
    exact ⟨y, (mem_latticeInside F h).2 hx, rfl⟩

/-- A deeper internal denominator is contained in every shallower one. -/
theorem latticeInside_le {m n₁ n₂ : ℤ} (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    latticeInside F (hm.trans h) ≤ latticeInside F hm := by
  intro x hx
  apply (mem_latticeInside F hm).2
  exact lattice_antitone F h ((mem_latticeInside F (hm.trans h)).1 hx)

/-- The honest additive quotient `lattice F m / lattice F n`, defined only from a certified
containment `m ≤ n`. -/
noncomputable abbrev LatticeQuotient (m n : ℤ) (h : m ≤ n) :=
  (lattice F m) ⧸ latticeInside F h

/-- The canonical linear quotient map from the numerator lattice. -/
noncomputable def latticeQuotientMk {m n : ℤ} (h : m ≤ n) :
    lattice F m →ₗ[ringOfIntegers F] LatticeQuotient F m n h :=
  (latticeInside F h).mkQ

@[simp]
theorem latticeQuotientMk_apply {m n : ℤ} (h : m ≤ n) (x : lattice F m) :
    latticeQuotientMk F h x = Submodule.Quotient.mk x :=
  rfl

/-- Every lattice-quotient class has a representative in its numerator lattice. -/
theorem latticeQuotientMk_surjective {m n : ℤ} (h : m ≤ n) :
    Function.Surjective (latticeQuotientMk F h) :=
  Submodule.mkQ_surjective (latticeInside F h)

/-- The canonical projection obtained by replacing a deeper denominator by a shallower one. -/
noncomputable def latticeQuotientProjection {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    LatticeQuotient F m n₂ (hm.trans h) →ₗ[ringOfIntegers F]
      LatticeQuotient F m n₁ hm :=
  Submodule.factor (latticeInside_le F hm h)

/-- The projection between nested lattice quotients keeps the chosen numerator representative. -/
@[simp]
theorem latticeQuotientProjection_mk {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) (x : lattice F m) :
    latticeQuotientProjection F hm h (latticeQuotientMk F (hm.trans h) x) =
      latticeQuotientMk F hm x :=
  rfl

/-- Projection to a quotient by a shallower denominator is surjective. -/
theorem latticeQuotientProjection_surjective {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    Function.Surjective (latticeQuotientProjection F hm h) :=
  Submodule.factor_surjective (latticeInside_le F hm h)

/-- Two numerator representatives define the same quotient class exactly when their difference
belongs to the denominator lattice. -/
@[simp]
theorem latticeQuotientMk_eq_mk_iff {m n : ℤ} (h : m ≤ n)
    {x y : lattice F m} :
    latticeQuotientMk F h x = latticeQuotientMk F h y ↔
      (x : F) - (y : F) ∈ lattice F n := by
  rw [latticeQuotientMk_apply, latticeQuotientMk_apply, Submodule.Quotient.eq,
    mem_latticeInside]
  rfl

/-- Equality of lattice-quotient representatives is equivalently congruence at the denominator
depth. -/
theorem latticeQuotientMk_eq_mk_iff_congruentAtDepth {m n : ℤ} (h : m ≤ n)
    {x y : lattice F m} :
    latticeQuotientMk F h x = latticeQuotientMk F h y ↔
      CongruentAtDepth n (x : F) (y : F) := by
  rw [latticeQuotientMk_eq_mk_iff F h]
  rfl

/-- A numerator representative is zero in the quotient exactly when it lies in the denominator
lattice. -/
@[simp]
theorem latticeQuotientMk_eq_zero_iff {m n : ℤ} (h : m ≤ n)
    {x : lattice F m} :
    latticeQuotientMk F h x = 0 ↔ (x : F) ∈ lattice F n := by
  rw [latticeQuotientMk_apply, Submodule.Quotient.mk_eq_zero, mem_latticeInside]

end Quotients

section AnnihilatorMembership

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The first annihilator calculation used in the manuscript's generic finite-duality pairing. -/
theorem forall_mul_div_mem_lattice_iff_left
    {Γ c : F} {M n r : ℤ} (hΓ : ord F Γ = ((M + n : ℤ) : WithTop ℤ)) :
    (∀ x : F, x ∈ lattice F r → c * x / Γ ∈ lattice F (-n)) ↔
      c ∈ lattice F (M - r) := by
  calc
    (∀ x : F, x ∈ lattice F r → c * x / Γ ∈ lattice F (-n)) ↔
        ∀ x : F, x ∈ lattice F r → c * x ∈ lattice F M := by
      apply forall_congr'
      intro x
      apply imp_congr_right
      intro _
      simpa using div_mem_lattice_iff F Γ (c * x) (M + n) (-n) hΓ
    _ ↔ c ∈ lattice F (M - r) := mul_lattice_subset_iff F

/-- The symmetric annihilator calculation used in the manuscript's generic finite-duality
pairing. -/
theorem forall_mul_div_mem_lattice_iff_right
    {Γ x : F} {M n q : ℤ} (hΓ : ord F Γ = ((M + n : ℤ) : WithTop ℤ)) :
    (∀ c : F, c ∈ lattice F (M - q) → c * x / Γ ∈ lattice F (-n)) ↔
      x ∈ lattice F q := by
  conv_rhs => rw [← show M - (M - q) = q by omega]
  rw [← mul_lattice_subset_iff F (c := x) (m := M) (n := M - q)]
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro _
  rw [mul_comm c x]
  simpa using div_mem_lattice_iff F Γ (x * c) (M + n) (-n) hΓ

end AnnihilatorMembership

end LanglandsFirstMainLemma
