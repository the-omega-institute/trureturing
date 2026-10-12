/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/UnitFiltration
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream unit-filtration support required by the retained local-field closure. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/LocalField/UnitFiltration.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths and explicit normal-subgroup instances and quotient parameters.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField.Lattices

/-!
# Unit filtration of a nonarchimedean local field

The zeroth layer is Mathlib's canonical valuation-subring unit group.  Positive layers are
principal units: membership in `U^(n+1)` means congruence to `1` modulo
`lattice F (n+1)`.  The file supplies the filtration laws, exact depth and ratio criteria,
certified quotients, and the distinct degree-zero and positive-degree graded interfaces.
-/

namespace LanglandsFirstMainLemma

open Filter Topology

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

noncomputable abbrev unitGroup : Subgroup Fˣ :=
  (ValuativeRel.valuation F).valuationSubring.unitGroup

theorem mem_unitGroup_iff_ord_eq_zero (u : Fˣ) :
    u ∈ unitGroup F ↔ ord F (u : F) = 0 := by
  rw [Valuation.mem_unitGroup_iff]
  constructor
  · intro hu
    have hi : (u : F) ∈ (ValuativeRel.valuation F).integer := by
      rw [Valuation.mem_integer_iff]
      simp [hu]
    have hii : ((u⁻¹ : Fˣ) : F) ∈ (ValuativeRel.valuation F).integer := by
      rw [Valuation.mem_integer_iff]
      simp [hu]
    have hnonneg : 0 ≤ ord F (u : F) :=
      (ord_nonneg_iff_mem_integer F _).2 hi
    have hinvnonneg : 0 ≤ ord F (((u⁻¹ : Fˣ) : F)) :=
      (ord_nonneg_iff_mem_integer F _).2 hii
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff F).2 (Units.ne_zero u))
    rw [← hk]
    rw [← hk] at hnonneg
    rw [Units.val_inv_eq_inv_val, ord_inv, ← hk,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg] at hinvnonneg
    simp only [WithTop.coe_nonneg] at hnonneg hinvnonneg
    congr
    omega
  · intro hu
    -- canonical valuation equality follows from integral membership in both directions
    apply le_antisymm
    · exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F)
          (u : F) 1).1
        ((ord_le_ord_iff F (1 : F) (u : F)).1 (by simp [hu]))
    · exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F)
          1 (u : F)).1
        ((ord_le_ord_iff F (u : F) (1 : F)).1 (by simp [hu]))

private theorem ord_eq_zero_of_congruentAtDepth_one {n : ℤ} {x : F}
    (hn : 0 < n) (hx : CongruentAtDepth n x 1) : ord F x = 0 := by
  have hdiff : (0 : WithTop ℤ) < ord F (x - 1) := by
    exact (WithTop.coe_lt_coe.mpr hn).trans_le hx
  have hne : ord F (x - 1) ≠ ord F 1 := by
    simpa only [ord_one] using ne_of_gt hdiff
  have hsum := ord_add_eq_min F hne
  rw [show x - 1 + 1 = x by ring] at hsum
  simpa only [ord_one, min_eq_right hdiff.le] using hsum

/-- The positive-depth principal units, retained as a subgroup of `Fˣ`. -/
private noncomputable def positiveUnitFiltration (n : ℕ) : Subgroup Fˣ where
  carrier := {u | u ∈ unitGroup F ∧
    CongruentAtDepth ((n + 1 : ℕ) : ℤ) (u : F) 1}
  one_mem' := ⟨(unitGroup F).one_mem, CongruentAtDepth.refl 1⟩
  mul_mem' := by
    rintro u v ⟨hu0, hu⟩ ⟨hv0, hv⟩
    refine ⟨(unitGroup F).mul_mem hu0 hv0, ?_⟩
    have hou : ord F (u : F) = 0 := (mem_unitGroup_iff_ord_eq_zero F u).1 hu0
    have h := CongruentAtDepth.mul (F := F) (n := ((n + 1 : ℕ) : ℤ))
      (a := (u : F)) (b := 1) (x := (v : F)) (y := 1)
      (by simp [hou]) (by simp) hu hv
    simpa using h
  inv_mem' := by
    rintro u ⟨hu0, hu⟩
    refine ⟨(unitGroup F).inv_mem hu0, ?_⟩
    have hou : ord F (u : F) = 0 := (mem_unitGroup_iff_ord_eq_zero F u).1 hu0
    have h := CongruentAtDepth.inv (F := F) (n := ((n + 1 : ℕ) : ℤ))
      (x := (u : F)) (y := 1) hou (by simp) hu
    simpa only [inv_one, Units.val_inv_eq_inv_val] using h

/-- The manuscript's unit filtration: `U⁰ = 𝓞_Fˣ`, while
`Uⁿ = 1 + 𝔭_Fⁿ` only at positive depths. -/
noncomputable def unitFiltration : ℕ → Subgroup Fˣ
  | 0 => unitGroup F
  | n + 1 => positiveUnitFiltration F n

@[simp]
theorem unitFiltration_zero : unitFiltration F 0 = unitGroup F := rfl

@[simp]
theorem mem_unitFiltration_zero (u : Fˣ) :
    u ∈ unitFiltration F 0 ↔ ord F (u : F) = 0 :=
  mem_unitGroup_iff_ord_eq_zero F u

@[simp]
theorem mem_unitFiltration_succ (n : ℕ) (u : Fˣ) :
    u ∈ unitFiltration F (n + 1) ↔
      CongruentAtDepth ((n + 1 : ℕ) : ℤ) (u : F) 1 := by
  change (u ∈ unitGroup F ∧
    CongruentAtDepth ((n + 1 : ℕ) : ℤ) (u : F) 1) ↔ _
  constructor
  · exact And.right
  · intro hu
    exact ⟨(mem_unitGroup_iff_ord_eq_zero F u).2
      (ord_eq_zero_of_congruentAtDepth_one F (by omega) hu), hu⟩

theorem mem_unitFiltration_succ_iff_sub_mem_lattice (n : ℕ) (u : Fˣ) :
    u ∈ unitFiltration F (n + 1) ↔
      (u : F) - 1 ∈ lattice F ((n + 1 : ℕ) : ℤ) := by
  rw [mem_unitFiltration_succ]
  rfl

theorem mem_unitFiltration_succ_iff_ord (n : ℕ) (u : Fˣ) :
    u ∈ unitFiltration F (n + 1) ↔
      (((n + 1 : ℕ) : ℤ) : WithTop ℤ) ≤ ord F ((u : F) - 1) := by
  rw [mem_unitFiltration_succ]
  rfl

theorem unitFiltration_le_unitGroup (n : ℕ) :
    unitFiltration F n ≤ unitGroup F := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
      intro u hu
      exact (show u ∈ unitGroup F ∧ _ from hu).1

/-- Increasing depth decreases the unit filtration. -/
theorem unitFiltration_antitone : Antitone (unitFiltration F) := by
  intro m n hmn
  cases m with
  | zero => exact unitFiltration_le_unitGroup F n
  | succ m =>
      cases n with
      | zero => omega
      | succ n =>
          intro u hu
          rw [mem_unitFiltration_succ] at hu ⊢
          apply CongruentAtDepth.mono (F := F) (n := ((n + 1 : ℕ) : ℤ))
            (m := ((m + 1 : ℕ) : ℤ)) ?_ hu
          exact_mod_cast hmn

theorem unitFiltration_antitone_of_le {m n : ℕ} (h : m ≤ n) :
    unitFiltration F n ≤ unitFiltration F m :=
  unitFiltration_antitone F h

/-! ## Topology -/

/-- Every unit-filtration layer is open in the field unit group. -/
theorem unitFiltration_isOpen (m : ℕ) :
    IsOpen (unitFiltration F m : Set Fˣ) := by
  cases m with
  | zero =>
      rw [unitFiltration_zero]
      have hsphere : IsOpen
          {x : F | (ValuativeRel.valuation F).restrict x = 1} :=
        (ValuativeRel.valuation F).isOpen_sphere one_ne_zero
      rw [show (unitGroup F : Set Fˣ) =
          (↑) ⁻¹' {x : F | (ValuativeRel.valuation F).restrict x = 1} by
        ext u
        change u ∈ (ValuativeRel.valuation F).valuationSubring.unitGroup ↔
          (ValuativeRel.valuation F).restrict (u : F) = 1
        rw [Valuation.mem_unitGroup_iff F (ValuativeRel.valuation F) u,
          (ValuativeRel.valuation F).restrict_eq_one_iff]]
      exact hsphere.preimage Units.continuous_val
  | succ m =>
      rw [show (unitFiltration F (m + 1) : Set Fˣ) =
          (fun u : Fˣ ↦ (u : F) - 1) ⁻¹'
            (lattice F ((m + 1 : ℕ) : ℤ) : Set F) by
        ext u
        exact mem_unitFiltration_succ_iff_sub_mem_lattice F m u]
      exact (lattice_isOpen F _).preimage
        (Units.continuous_val.sub continuous_const)

/-- The positive unit filtrations form a neighborhood basis of one in the field unit group. -/
theorem unitFiltration_hasBasis_nhds_one :
    (nhds (1 : Fˣ)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (unitFiltration F (n + 1) : Set Fˣ) := by
  have hfield :
      (nhds (1 : F)).HasBasis (fun _ : ℤ ↦ True) fun n ↦
        {x : F | x - 1 ∈ lattice F n} :=
    (lattice_nhds_zero_hasBasis F).nhds_of_zero 1
  have hunits :
      (nhds (1 : Fˣ)).HasBasis (fun _ : ℤ ↦ True) fun n ↦
        {u : Fˣ | (u : F) - 1 ∈ lattice F n} := by
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap (1 : Fˣ)]
    simpa only [Units.val_one, Set.preimage_setOf_eq] using
      hfield.comap ((↑) : Fˣ → F)
  refine hunits.to_hasBasis ?_ ?_
  · intro r _
    cases r with
    | ofNat r =>
        refine ⟨r, trivial, ?_⟩
        intro u hu
        exact lattice_antitone F ((Int.ofNat_le).2 (Nat.le_succ r))
          ((mem_unitFiltration_succ_iff_sub_mem_lattice F r u).1 hu)
    | negSucc r =>
        refine ⟨0, trivial, ?_⟩
        intro u hu
        exact lattice_antitone F (by omega)
          ((mem_unitFiltration_succ_iff_sub_mem_lattice F 0 u).1 hu)
  · intro n _
    refine ⟨((n + 1 : ℕ) : ℤ), trivial, ?_⟩
    intro u hu
    exact (mem_unitFiltration_succ_iff_sub_mem_lattice F n u).2 hu

/-- A family of units eventually lying in positive layers whose depths tend to infinity converges
to one in the field unit group. -/
theorem tendsto_one_of_eventually_mem_unitFiltration
    {ι : Type*} {l : Filter ι} {d : ι → ℕ} {u : ι → Fˣ}
    (hd : Tendsto d l atTop)
    (hu : ∀ᶠ i in l, u i ∈ unitFiltration F (d i + 1)) :
    Tendsto u l (nhds 1) := by
  rw [(unitFiltration_hasBasis_nhds_one F).tendsto_right_iff]
  intro n _
  filter_upwards [hd.eventually (eventually_ge_atTop n), hu] with i hi hui
  exact unitFiltration_antitone F (Nat.add_le_add_right hi 1) hui

/-- Field-valued form of convergence through arbitrarily deep positive unit filtrations. -/
theorem tendsto_coe_one_of_eventually_mem_unitFiltration
    {ι : Type*} {l : Filter ι} {d : ι → ℕ} {u : ι → Fˣ}
    (hd : Tendsto d l atTop)
    (hu : ∀ᶠ i in l, u i ∈ unitFiltration F (d i + 1)) :
    Tendsto (fun i ↦ (u i : F)) l (nhds 1) := by
  have hval : Tendsto ((↑) : Fˣ → F) (nhds 1) (nhds 1) := by
    simpa using Units.continuous_val.tendsto (1 : Fˣ)
  exact hval.comp (tendsto_one_of_eventually_mem_unitFiltration F hd hu)

/-- The canonical equivalence from `U⁰` to the units of the valuation ring. -/
noncomputable abbrev unitGroupMulEquivRingOfIntegers :
    unitGroup F ≃* (ringOfIntegers F)ˣ :=
  (ValuativeRel.valuation F).valuationSubring.unitGroupMulEquiv

/-- The first positive layer agrees with Mathlib's canonical principal-unit group. -/
theorem unitFiltration_one_eq_principalUnitGroup :
    unitFiltration F 1 =
      (ValuativeRel.valuation F).valuationSubring.principalUnitGroup := by
  let A := (ValuativeRel.valuation F).valuationSubring
  ext u
  rw [mem_unitFiltration_succ_iff_sub_mem_lattice]
  change ((u : F) - 1 ∈ lattice F 1) ↔ A.valuation ((u : F) - 1) < 1
  rw [← A.mem_nonunits_iff, A.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · intro hu
    have hu0 : (u : F) - 1 ∈ ringOfIntegers F :=
      (mem_lattice_zero_iff F).1 (lattice_antitone F (show (0 : ℤ) ≤ 1 by omega) hu)
    exact ⟨hu0, (mem_lattice_one_iff_mem_maximalIdeal F ⟨_, hu0⟩).1 hu⟩
  · rintro ⟨hu0, hu⟩
    exact (mem_lattice_one_iff_mem_maximalIdeal F ⟨_, hu0⟩).2 hu

/-- Products from different layers lie in the shallower of the two layers. -/
theorem unitFiltration_mul_mem_min {m n : ℕ} {u v : Fˣ}
    (hu : u ∈ unitFiltration F m) (hv : v ∈ unitFiltration F n) :
    u * v ∈ unitFiltration F (min m n) := by
  exact (unitFiltration F (min m n)).mul_mem
    (unitFiltration_antitone F (min_le_left m n) hu)
    (unitFiltration_antitone F (min_le_right m n) hv)

/-- Same-layer multiplication is the subgroup multiplication interface. -/
theorem unitFiltration_mul_mem {n : ℕ} {u v : Fˣ}
    (hu : u ∈ unitFiltration F n) (hv : v ∈ unitFiltration F n) :
    u * v ∈ unitFiltration F n :=
  (unitFiltration F n).mul_mem hu hv

/-- Every layer is closed under inversion. -/
theorem unitFiltration_inv_mem {n : ℕ} {u : Fˣ}
    (hu : u ∈ unitFiltration F n) : u⁻¹ ∈ unitFiltration F n :=
  (unitFiltration F n).inv_mem hu

/-- Inversion preserves the exact order of the displacement from `1` for local units. -/
theorem ord_inv_sub_one_eq (u : Fˣ) (hu : u ∈ unitGroup F) :
    ord F (((u⁻¹ : Fˣ) : F) - 1) = ord F ((u : F) - 1) := by
  have hu0 : (u : F) ≠ 0 := Units.ne_zero u
  have hord : ord F (u : F) = 0 := (mem_unitGroup_iff_ord_eq_zero F u).1 hu
  rw [Units.val_inv_eq_inv_val, ← one_div, div_sub_one hu0, ord_div,
    ord_sub_swap, hord]
  simp

/-- Exact positive depth is invariant under inversion. -/
theorem mem_unitFiltration_inv_iff (n : ℕ) (u : Fˣ) :
    u⁻¹ ∈ unitFiltration F (n + 1) ↔ u ∈ unitFiltration F (n + 1) := by
  constructor
  · intro hu
    simpa using (unitFiltration F (n + 1)).inv_mem hu
  · exact (unitFiltration F (n + 1)).inv_mem

/-- The exact positive-depth shell is detected by the order of `u - 1`. -/
theorem mem_unitFiltration_and_not_mem_succ_iff (n : ℕ) (u : Fˣ) :
    u ∈ unitFiltration F (n + 1) ∧ u ∉ unitFiltration F (n + 2) ↔
      ord F ((u : F) - 1) = (((n + 1 : ℕ) : ℤ) : WithTop ℤ) := by
  rw [mem_unitFiltration_succ_iff_sub_mem_lattice,
    mem_unitFiltration_succ_iff_sub_mem_lattice]
  have hd : ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by omega
  rw [hd]
  exact mem_lattice_and_not_mem_succ_iff F

/-- A positive-depth lattice element gives the principal unit `1 + x`. -/
noncomputable def principalUnitOf (n : ℕ) (x : F)
    (hx : x ∈ lattice F ((n + 1 : ℕ) : ℤ)) : Fˣ :=
  Units.mk0 (1 + x) (by
    have hcong : CongruentAtDepth ((n + 1 : ℕ) : ℤ) (1 + x) 1 := by
      simpa [CongruentAtDepth] using hx
    have hord := ord_eq_zero_of_congruentAtDepth_one F (by omega) hcong
    intro hzero
    simp [hzero] at hord)

@[simp]
theorem coe_principalUnitOf (n : ℕ) (x : F)
    (hx : x ∈ lattice F ((n + 1 : ℕ) : ℤ)) :
    (principalUnitOf F n x hx : F) = 1 + x := rfl

theorem principalUnitOf_mem (n : ℕ) (x : F)
    (hx : x ∈ lattice F ((n + 1 : ℕ) : ℤ)) :
    principalUnitOf F n x hx ∈ unitFiltration F (n + 1) := by
  rw [mem_unitFiltration_succ_iff_sub_mem_lattice]
  simpa using hx

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The error in replacing multiplication of principal units by addition of their
displacements is their product. -/
theorem unit_mul_sub_one_sub_add (u v : Fˣ) :
    (((u * v : Fˣ) : F) - 1) - (((u : F) - 1) + ((v : F) - 1)) =
      ((u : F) - 1) * ((v : F) - 1) := by
  change (u : F) * (v : F) - 1 - ((u : F) - 1 + ((v : F) - 1)) = _
  ring

/-- The multiplication-linearization error has the sum of the two positive depths. -/
theorem unitFiltration_mul_error_mem {m n : ℕ} {u v : Fˣ}
    (hu : u ∈ unitFiltration F (m + 1))
    (hv : v ∈ unitFiltration F (n + 1)) :
    (((u * v : Fˣ) : F) - 1) - (((u : F) - 1) + ((v : F) - 1)) ∈
      lattice F (((m + 1 : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ)) := by
  rw [unit_mul_sub_one_sub_add]
  exact mul_mem_lattice F
    ((mem_unitFiltration_succ_iff_sub_mem_lattice F m u).1 hu)
    ((mem_unitFiltration_succ_iff_sub_mem_lattice F n v).1 hv)

/-- On every positive graded layer, multiplication is addition modulo the next lattice. -/
theorem unitFiltration_mul_error_mem_next (n : ℕ) {u v : Fˣ}
    (hu : u ∈ unitFiltration F (n + 1))
    (hv : v ∈ unitFiltration F (n + 1)) :
    (((u * v : Fˣ) : F) - 1) - (((u : F) - 1) + ((v : F) - 1)) ∈
      lattice F ((n + 2 : ℕ) : ℤ) := by
  apply lattice_antitone F (m := ((n + 2 : ℕ) : ℤ))
    (n := (((n + 1 : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ))) (by omega)
  exact unitFiltration_mul_error_mem F hu hv

/-- Dividing by a local unit does not change the order of a difference. -/
theorem ord_div_sub_one_eq_ord_sub (u v : Fˣ) (hv : v ∈ unitGroup F) :
    ord F ((u : F) / (v : F) - 1) = ord F ((u : F) - (v : F)) := by
  have hv0 : (v : F) ≠ 0 := Units.ne_zero v
  have hord : ord F (v : F) = 0 := (mem_unitGroup_iff_ord_eq_zero F v).1 hv
  rw [div_sub_one hv0, ord_div, hord]
  simp

/-- For local units, quotient membership is exactly depth congruence of the representatives. -/
theorem div_mem_unitFiltration_iff_congruentAtDepth (n : ℕ) (u v : Fˣ)
    (hu : u ∈ unitGroup F) (hv : v ∈ unitGroup F) :
    u / v ∈ unitFiltration F n ↔
      CongruentAtDepth (n : ℤ) (u : F) (v : F) := by
  cases n with
  | zero =>
      constructor
      · intro _
        rw [CongruentAtDepth]
        have h := ord_sub F (u : F) (v : F)
        rw [(mem_unitGroup_iff_ord_eq_zero F u).1 hu,
          (mem_unitGroup_iff_ord_eq_zero F v).1 hv] at h
        simpa using h
      · intro _
        exact (unitGroup F).div_mem hu hv
  | succ n =>
      rw [mem_unitFiltration_succ_iff_ord]
      simp only [Units.val_div_eq_div_val]
      rw [CongruentAtDepth]
      rw [ord_div_sub_one_eq_ord_sub F u v hv]

section UnitQuotients

/-- The certified copy of `Uⁿ` inside `Uᵐ`, for `m ≤ n`. -/
noncomputable def unitFiltrationInside {m n : ℕ} (_h : m ≤ n) :
    Subgroup (unitFiltration F m) :=
  (Subgroup.inclusion (unitFiltration_antitone F _h)).range

@[simp]
theorem mem_unitFiltrationInside {m n : ℕ} (h : m ≤ n)
    (u : unitFiltration F m) :
    u ∈ unitFiltrationInside F h ↔ (u : Fˣ) ∈ unitFiltration F n := by
  constructor
  · rintro ⟨v, hv⟩
    rw [← congrArg Subtype.val hv]
    exact v.property
  · intro hu
    exact ⟨⟨u, hu⟩, rfl⟩

/-- Mapping the internal denominator back to `Fˣ` gives the stated deeper layer. -/
@[simp]
theorem map_unitFiltrationInside_subtype {m n : ℕ} (h : m ≤ n) :
    (unitFiltrationInside F h).map (unitFiltration F m).subtype =
      unitFiltration F n := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_unitFiltrationInside F h v).1 hv
  · intro hu
    let v : unitFiltration F m := ⟨u, unitFiltration_antitone F h hu⟩
    exact ⟨v, (mem_unitFiltrationInside F h v).2 hu, rfl⟩

/-- A deeper internal denominator is contained in every shallower one. -/
theorem unitFiltrationInside_le {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    unitFiltrationInside F (hm.trans h) ≤ unitFiltrationInside F hm := by
  intro u hu
  apply (mem_unitFiltrationInside F hm u).2
  exact unitFiltration_antitone F h
    ((mem_unitFiltrationInside F (hm.trans h) u).1 hu)

/-- An honest unit-filtration quotient `Uᵐ/Uⁿ`, available only with certified
containment `m ≤ n`. -/
noncomputable abbrev UnitFiltrationQuotient (m n : ℕ) (h : m ≤ n) :=
  (unitFiltration F m) ⧸ unitFiltrationInside F h

/-- The canonical quotient homomorphism from `Uᵐ`. -/
noncomputable def unitFiltrationQuotientMk {m n : ℕ} (h : m ≤ n) :
    unitFiltration F m →* UnitFiltrationQuotient F m n h :=
  QuotientGroup.mk' (unitFiltrationInside F h)

@[simp]
theorem unitFiltrationQuotientMk_apply {m n : ℕ} (h : m ≤ n)
    (u : unitFiltration F m) :
    unitFiltrationQuotientMk F h u = QuotientGroup.mk u := rfl

theorem unitFiltrationQuotientMk_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (unitFiltrationQuotientMk F h) :=
  QuotientGroup.mk'_surjective (unitFiltrationInside F h)

@[simp]
theorem unitFiltrationQuotientMk_eq_mk_iff {m n : ℕ} (h : m ≤ n)
    (u v : unitFiltration F m) :
    unitFiltrationQuotientMk F h u = unitFiltrationQuotientMk F h v ↔
      (u : Fˣ) / (v : Fˣ) ∈ unitFiltration F n := by
  rw [unitFiltrationQuotientMk_apply, unitFiltrationQuotientMk_apply,
    QuotientGroup.eq_iff_div_mem, mem_unitFiltrationInside]
  simp only [Subgroup.coe_div]

@[simp]
theorem unitFiltrationQuotientMk_eq_one_iff {m n : ℕ} (h : m ≤ n)
    (u : unitFiltration F m) :
    unitFiltrationQuotientMk F h u = 1 ↔
      (u : Fˣ) ∈ unitFiltration F n := by
  rw [unitFiltrationQuotientMk_apply, QuotientGroup.eq_one_iff,
    mem_unitFiltrationInside]

theorem unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth
    {m n : ℕ} (h : m ≤ n) (u v : unitFiltration F m) :
    unitFiltrationQuotientMk F h u = unitFiltrationQuotientMk F h v ↔
      CongruentAtDepth (n : ℤ) ((u : Fˣ) : F) ((v : Fˣ) : F) := by
  rw [unitFiltrationQuotientMk_eq_mk_iff]
  exact div_mem_unitFiltration_iff_congruentAtDepth F n _ _
    (unitFiltration_le_unitGroup F m u.property)
    (unitFiltration_le_unitGroup F m v.property)

/-- Replacing a deeper denominator by a shallower denominator. -/
noncomputable def unitFiltrationQuotientProjection {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    UnitFiltrationQuotient F m n₂ (hm.trans h) →*
      UnitFiltrationQuotient F m n₁ hm :=
  QuotientGroup.lift (unitFiltrationInside F (hm.trans h))
    (unitFiltrationQuotientMk F hm) (by
      intro u hu
      rw [MonoidHom.mem_ker, unitFiltrationQuotientMk_eq_one_iff]
      exact (mem_unitFiltrationInside F hm u).1
        (unitFiltrationInside_le F hm h hu))

@[simp]
theorem unitFiltrationQuotientProjection_mk {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) (u : unitFiltration F m) :
    unitFiltrationQuotientProjection F hm h
        (unitFiltrationQuotientMk F (hm.trans h) u) =
      unitFiltrationQuotientMk F hm u := rfl

theorem unitFiltrationQuotientProjection_surjective {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    Function.Surjective (unitFiltrationQuotientProjection F hm h) :=
  QuotientGroup.lift_surjective_of_surjective
    (unitFiltrationInside F (hm.trans h)) (unitFiltrationQuotientMk F hm)
    (unitFiltrationQuotientMk_surjective F hm) _

/-- The `n`-th graded unit quotient `Uⁿ/Uⁿ⁺¹`. -/
noncomputable abbrev UnitGradedPiece (n : ℕ) :=
  UnitFiltrationQuotient F n (n + 1) (Nat.le_succ n)

/-- The canonical representative map to `grⁿ U`. -/
noncomputable def unitGradedMk (n : ℕ) :
    unitFiltration F n →* UnitGradedPiece F n :=
  unitFiltrationQuotientMk F (Nat.le_succ n)

theorem unitGradedMk_surjective (n : ℕ) :
    Function.Surjective (unitGradedMk F n) :=
  unitFiltrationQuotientMk_surjective F (Nat.le_succ n)

@[simp]
theorem unitGradedMk_eq_mk_iff (n : ℕ) (u v : unitFiltration F n) :
    unitGradedMk F n u = unitGradedMk F n v ↔
      CongruentAtDepth ((n + 1 : ℕ) : ℤ)
        ((u : Fˣ) : F) ((v : Fˣ) : F) :=
  unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F (Nat.le_succ n) u v

@[simp]
theorem unitGradedMk_eq_one_iff (n : ℕ) (u : unitFiltration F n) :
    unitGradedMk F n u = 1 ↔ (u : Fˣ) ∈ unitFiltration F (n + 1) :=
  unitFiltrationQuotientMk_eq_one_iff F (Nat.le_succ n) u

/-- The degree-zero graded quotient is the multiplicative group of the residue field. -/
noncomputable def unitGradedZeroEquivResidueFieldUnits :
    UnitGradedPiece F 0 ≃*
      (IsLocalRing.ResidueField
        ((ValuativeRel.valuation F).valuationSubring))ˣ := by
  let A := (ValuativeRel.valuation F).valuationSubring
  have hden : unitFiltrationInside F (show 0 ≤ 1 by omega) =
      A.principalUnitGroup.comap A.unitGroup.subtype := by
    ext u
    rw [mem_unitFiltrationInside]
    change (u : Fˣ) ∈ unitFiltration F 1 ↔
      (u : Fˣ) ∈ A.principalUnitGroup
    rw [unitFiltration_one_eq_principalUnitGroup F]
  letI : (unitFiltrationInside F (show 0 ≤ 1 by omega)).Normal :=
    { conj_mem := by
        intro b hb a
        have hconj : a * b * a⁻¹ = b := by
          apply Subtype.ext
          change (a : Fˣ) * (b : Fˣ) * (a : Fˣ)⁻¹ = (b : Fˣ)
          calc
            (a : Fˣ) * (b : Fˣ) * (a : Fˣ)⁻¹ =
                (b : Fˣ) * (a : Fˣ) * (a : Fˣ)⁻¹ := by
                  rw [mul_comm (a : Fˣ) (b : Fˣ)]
            _ = (b : Fˣ) := by simp
        rw [hconj]
        exact hb }
  letI : (A.principalUnitGroup.comap A.unitGroup.subtype).Normal :=
    { conj_mem := by
        intro b hb a
        have hconj : a * b * a⁻¹ = b := by
          apply Subtype.ext
          change (a : Fˣ) * (b : Fˣ) * (a : Fˣ)⁻¹ = (b : Fˣ)
          calc
            (a : Fˣ) * (b : Fˣ) * (a : Fˣ)⁻¹ =
                (b : Fˣ) * (a : Fˣ) * (a : Fˣ)⁻¹ := by
                  rw [mul_comm (a : Fˣ) (b : Fˣ)]
            _ = (b : Fˣ) := by simp
        rw [hconj]
        exact hb }
  exact (QuotientGroup.quotientMulEquivOfEq
    (M := unitFiltrationInside F (show 0 ≤ 1 by omega))
    (N := A.principalUnitGroup.comap A.unitGroup.subtype) hden).trans
    A.unitsModPrincipalUnitsEquivResidueFieldUnits

/-- The additive graded quotient of two successive valuation lattices. -/
noncomputable abbrev LatticeGradedPiece (r : ℤ) :=
  LatticeQuotient F r (r + 1) (by omega)

/-- The displacement `u - 1`, as an element of the positive-depth numerator lattice. -/
noncomputable def unitFiltrationDisplacement (n : ℕ)
    (u : unitFiltration F (n + 1)) : lattice F ((n + 1 : ℕ) : ℤ) :=
  ⟨((u : Fˣ) : F) - 1,
    (mem_unitFiltration_succ_iff_sub_mem_lattice F n (u : Fˣ)).1 u.property⟩

@[simp]
theorem coe_unitFiltrationDisplacement (n : ℕ)
    (u : unitFiltration F (n + 1)) :
    (unitFiltrationDisplacement F n u : F) = ((u : Fˣ) : F) - 1 := rfl

/-- On a positive layer, `u ↦ u - 1` is multiplicative-to-additive modulo the
next lattice. -/
noncomputable def positiveUnitToLatticeGraded (n : ℕ) :
    unitFiltration F (n + 1) →*
      Multiplicative (LatticeGradedPiece F ((n + 1 : ℕ) : ℤ)) := by
  let r : ℤ := ((n + 1 : ℕ) : ℤ)
  let h : r ≤ r + 1 := by omega
  exact
    { toFun := fun u ↦ Multiplicative.ofAdd
        (latticeQuotientMk F h (unitFiltrationDisplacement F n u))
      map_one' := by
        apply Multiplicative.toAdd.injective
        change latticeQuotientMk F h (unitFiltrationDisplacement F n 1) = 0
        rw [latticeQuotientMk_eq_zero_iff]
        simp
      map_mul' := by
        intro u v
        apply Multiplicative.toAdd.injective
        change latticeQuotientMk F h (unitFiltrationDisplacement F n (u * v)) =
          latticeQuotientMk F h (unitFiltrationDisplacement F n u) +
            latticeQuotientMk F h (unitFiltrationDisplacement F n v)
        rw [← map_add]
        apply (latticeQuotientMk_eq_mk_iff F h).2
        apply lattice_antitone F (show r + 1 ≤ r + r by dsimp [r]; omega)
        have hprod := mul_mem_lattice F
          (unitFiltrationDisplacement F n u).property
          (unitFiltrationDisplacement F n v).property
        convert hprod using 1
        change (((((u * v : unitFiltration F (n + 1)) : Fˣ) : F) - 1) -
          ((((u : Fˣ) : F) - 1) + (((v : Fˣ) : F) - 1))) =
            (((u : Fˣ) : F) - 1) * (((v : Fˣ) : F) - 1)
        change ((u : Fˣ) : F) * ((v : Fˣ) : F) - 1 -
          ((((u : Fˣ) : F) - 1) + (((v : Fˣ) : F) - 1)) = _
        ring }

@[simp]
theorem positiveUnitToLatticeGraded_apply (n : ℕ)
    (u : unitFiltration F (n + 1)) :
    Multiplicative.toAdd (positiveUnitToLatticeGraded F n u) =
      latticeQuotientMk F (show ((n + 1 : ℕ) : ℤ) ≤
          ((n + 1 : ℕ) : ℤ) + 1 by omega)
        (unitFiltrationDisplacement F n u) := rfl

theorem positiveUnitToLatticeGraded_surjective (n : ℕ) :
    Function.Surjective (positiveUnitToLatticeGraded F n) := by
  let r : ℤ := ((n + 1 : ℕ) : ℤ)
  let h : r ≤ r + 1 := by omega
  intro z
  obtain ⟨x, hx⟩ := latticeQuotientMk_surjective F h (Multiplicative.toAdd z)
  let u₀ : Fˣ := principalUnitOf F n (x : F) x.property
  let u : unitFiltration F (n + 1) := ⟨u₀, principalUnitOf_mem F n (x : F) x.property⟩
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [positiveUnitToLatticeGraded_apply]
  calc
    latticeQuotientMk F _ (unitFiltrationDisplacement F n u) =
        latticeQuotientMk F h x := by
      congr 1
      apply Subtype.ext
      simp [unitFiltrationDisplacement, u, u₀]
    _ = Multiplicative.toAdd z := hx

theorem positiveUnitToLatticeGraded_ker (n : ℕ) :
    (positiveUnitToLatticeGraded F n).ker =
      unitFiltrationInside F (Nat.le_succ (n + 1)) := by
  ext u
  rw [MonoidHom.mem_ker, mem_unitFiltrationInside]
  change Multiplicative.ofAdd
      (latticeQuotientMk F _ (unitFiltrationDisplacement F n u)) = 1 ↔
    (u : Fˣ) ∈ unitFiltration F (n + 2)
  rw [ofAdd_eq_one, latticeQuotientMk_eq_zero_iff,
    mem_unitFiltration_succ_iff_sub_mem_lattice]
  have hd : ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by omega
  rw [hd]
  rfl

/-- At positive depth, `u ↦ u - 1` identifies the multiplicative unit graded piece
with the multiplicativization of the corresponding additive lattice graded piece. -/
noncomputable def positiveUnitGradedEquivLattice (n : ℕ) :
    UnitGradedPiece F (n + 1) ≃*
      Multiplicative (LatticeGradedPiece F ((n + 1 : ℕ) : ℤ)) :=
  QuotientGroup.liftEquiv (unitFiltrationInside F (Nat.le_succ (n + 1)))
    (positiveUnitToLatticeGraded_surjective F n)
    (positiveUnitToLatticeGraded_ker F n).symm

@[simp]
theorem positiveUnitGradedEquivLattice_mk (n : ℕ)
    (u : unitFiltration F (n + 1)) :
    positiveUnitGradedEquivLattice F n (unitGradedMk F (n + 1) u) =
      positiveUnitToLatticeGraded F n u := rfl

/-- Additive form of the positive graded identification. -/
noncomputable def positiveUnitGradedAddEquivLattice (n : ℕ) :
    Additive (UnitGradedPiece F (n + 1)) ≃+
      LatticeGradedPiece F ((n + 1 : ℕ) : ℤ) :=
  MulEquiv.toAdditiveLeft (positiveUnitGradedEquivLattice F n)

end UnitQuotients

end LanglandsFirstMainLemma
