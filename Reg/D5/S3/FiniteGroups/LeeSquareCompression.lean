import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.LeeSquareCompression
import Reg.Support.DependentFamily

/-! Exact source families for square lifting and arbitrary coefficient pairs. -/
namespace Reg.D5.S3.FiniteGroups.LeeSquareCompression
open _root_.D5.S3.FiniteGroups.LeeSquareCompression
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity (sumDiff sumDiff_index sumDiff_injective)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

def residueMap (n : ℕ) : Plane →+ (Fin 2 → ZMod n) where
  toFun z := fun i => (z i : ZMod n)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp
def grid (n : ℕ) : Submodule ℤ Plane := (residueMap n).toIntLinearMap.ker
private theorem grid_div (n : ℕ) {z : Plane} (hz : z ∈ grid n) :
    (n : ℤ) ∣ z 0 ∧ (n : ℤ) ∣ z 1 := by
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hz 0),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hz 1)⟩
theorem grid_cover (t : ℕ) : ∀ z : Plane, ∃ r : Plane,
    |r 0|+|r 1| ≤ (2*t : ℤ) ∧ z-r ∈ grid (2*t+1) := by
  intro z
  let r : Plane := fun i => (z i+t)%(2*t+1)-t
  have hb (i : Fin 2) : |r i| ≤ (t : ℤ) := by
    have h0 := Int.emod_nonneg (z i+t) (show (2*t+1 : ℤ) ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos (z i+t) (show (0 : ℤ) < 2*t+1 by omega)
    apply abs_le.mpr
    dsimp [r]
    omega
  refine ⟨r,by linarith [hb 0,hb 1],?_⟩
  change residueMap (2*t+1) (z-r) = 0
  ext i
  change ((z i-r i : ℤ) : ZMod (2*t+1)) = 0
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  refine ⟨(z i+t)/(2*t+1),?_⟩
  have he := Int.mul_ediv_add_emod (z i+t) (2*t+1)
  change z i-((z i+t)%(2*t+1)-t) = (2*t+1)*((z i+t)/(2*t+1))
  omega
theorem grid_hole (n : ℕ) (hn : 0 < n) (hodd : Odd (n : ℤ)) :
    ¬ SquareCovers ((grid n).map sumDiff) ((n : ℤ)-1) := by
  intro h
  obtain ⟨r,hr,u,hu,he⟩ := h ![(n : ℤ),0]
  obtain ⟨hu0,hu1⟩ := grid_div n hu
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  change u 0+u 1 = (n : ℤ)-r 0 at h0
  change u 0-u 1 = 0-r 1 at h1
  have hd0 : (n : ℤ) ∣ r 0 := by
    convert (dvd_refl (n : ℤ)).sub (hu0.add hu1) using 1
    omega
  have hd1 : (n : ℤ) ∣ r 1 := by
    convert (dvd_neg.mpr (hu0.sub hu1)) using 1
    omega
  have hr0 := abs_le.mp hr.1
  have hr1 := abs_le.mp hr.2
  obtain ⟨x,hx⟩ := hd0
  obtain ⟨y,hy⟩ := hd1
  have hx0 : x = 0 := by nlinarith
  have hy0 : y = 0 := by nlinarith
  obtain ⟨d,hd⟩ := hodd
  subst x
  subst y
  omega
private theorem range_hole_zero : ¬ SquareCovers ((⊤ : Submodule ℤ Plane).map sumDiff) 0 := by
  intro h
  obtain ⟨r,hr,u,_,he⟩ := h ![1,0]
  have hr0 := abs_le.mp hr.1
  have hr1 := abs_le.mp hr.2
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  change u 0+u 1 = 1-r 0 at h0
  change u 0-u 1 = 0-r 1 at h1
  omega
private def smallMap : Plane →+ Target 2 1 where
  toFun z := ((z 0 : ZMod 2),(z 1 : ZMod 2))
  map_zero' := by simp
  map_add' z w := by simp
private theorem small_surj : Function.Surjective smallMap := by
  rintro ⟨a,b⟩
  exact ⟨![(a.val : ℤ),(b.val : ℤ)],by ext <;> simp [smallMap]⟩
private theorem small_cover : ∀ g : Target 2 1, ∃ x y : ℤ,
    |x|+|y| ≤ 3 ∧ x • ((1,0) : Target 2 1)+y • ((0,1) : Target 2 1) = g := by
  rintro ⟨a,b⟩
  refine ⟨a.val,b.val,?_,?_⟩
  · have ha := a.val_lt
    have hb := b.val_lt
    simp only [Int.abs_natCast]
    omega
  · apply Prod.ext <;> simp [zsmul_eq_mul]

abbrev holeSignature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def holeActual : Realization holeSignature := realize holeSignature
  (fun _ _ c => c) (fun e => nomatch e)
noncomputable def holeRejected : Realization holeSignature := realize holeSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev holeArena : Arena where
  signature := holeSignature
  Law R := ∀ (K : Submodule ℤ Plane) {c s : ℤ} (_ : Odd c)
    (_ : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1)
    (_ : ∀ z : Plane, ∃ r : Plane, |r 0|+|r 1| ≤ s ∧ z-r ∈ K)
    (_ : ¬ SquareCovers (K.map sumDiff) s), R.readout () () c ∣ s+1
private theorem holeRejected_law : ¬ holeArena.Law holeRejected := by
  intro h
  have hh := h (⊤ : Submodule ℤ Plane) (c := 1) (s := 0) (by decide)
    (by intros; simp) (by intro z; exact ⟨0,by simp,Submodule.mem_top⟩) range_hole_zero
  norm_num [holeRejected,realize] at hh
noncomputable def holeSource : Registration holeArena (type_of% (@square_hole_forces_radius_divisibility)) where
  actual := holeActual
  bridge := Iff.rfl
  variation := ⟨square_hole_forces_radius_divisibility, holeRejected, holeRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨holeRejected, ?_, rfl, holeRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(),0,1,by norm_num [holeActual,realize]⟩
noncomputable def holeRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@square_hole_forces_radius_divisibility) (Realization holeSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.LeeSquareCompression.square_hole_forces_radius_divisibility.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.LeeSquareCompression.holeSource
  realizationSource := none
  generated := false
  arena := .source ⟨holeArena⟩
  objectArena := .source ⟨holeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source holeArena ⟨holeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize holeSignature (fun _ _ c => c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.LeeSquareCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev kernelSignature : Signature where
  Params := Unit
  State _ := Plane
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def kernelActual : Realization kernelSignature := realize kernelSignature
  (fun _ _ z => z 0) (fun e => nomatch e)
noncomputable def kernelRejected : Realization kernelSignature := realize kernelSignature
  (fun _ _ _ => 1) (fun e => nomatch e)
abbrev kernelArena : Arena where
  signature := kernelSignature
  Law R := ∀ {c k : ℕ} (_ : 0 < c) (f : Plane →+ Target c k)
    (_ : Function.Surjective f) {z : Plane} (_ : f z = 0),
    (c : ℤ) ∣ R.readout () () z ∧ (c : ℤ) ∣ z 1
private theorem kernelRejected_law : ¬ kernelArena.Law kernelRejected := by
  intro h
  have hh := h (by decide : 0 < (2 : ℕ)) smallMap small_surj (z := 0) (map_zero smallMap)
  norm_num [kernelRejected,realize] at hh
noncomputable def kernelSource : Registration kernelArena (type_of% (@kernel_coordinates_dvd)) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨kernel_coordinates_dvd, kernelRejected, kernelRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨kernelRejected, ?_, rfl, kernelRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(),![0,0],![1,0],by norm_num [kernelActual,realize]⟩
noncomputable def kernelRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@kernel_coordinates_dvd) (Realization kernelSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.LeeSquareCompression.kernel_coordinates_dvd.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.LeeSquareCompression.kernelSource
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨kernelSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature (fun _ _ z => z 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.LeeSquareCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev liftSignature : Signature where
  Params := Unit
  State _ := Submodule ℤ Plane
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def liftActual : Realization liftSignature := realize liftSignature
  (fun _ _ K => (K.toAddSubgroup.index : ℤ)) (fun e => nomatch e)
noncomputable def liftRejected : Realization liftSignature := realize liftSignature
  (fun _ _ _ => 1000) (fun e => nomatch e)
abbrev liftArena : Arena where
  signature := liftSignature
  Law R := ∀ (K : Submodule ℤ Plane) {c s : ℤ} (_ : 3 ≤ c) (_ : Odd c) (_ : 3 ≤ s)
    (_ : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1)
    (_ : ∀ z : Plane, ∃ r : Plane, |r 0|+|r 1| ≤ s ∧ z-r ∈ K)
    (_ : 2*s^2 < R.readout () () K), SquareCovers (K.map sumDiff) s
private theorem liftRejected_law : ¬ liftArena.Law liftRejected := by
  intro h
  have hh := h (grid 5) (c := 5) (s := 4) (by norm_num) (by decide) (by norm_num)
    (fun _ hz => grid_div 5 hz) (by simpa using grid_cover 2) (by norm_num [liftRejected,realize])
  exact grid_hole 5 (by decide) (by decide) hh
noncomputable def liftSource : Registration liftArena (type_of% (@large_index_square_lift)) where
  actual := liftActual
  bridge := Iff.rfl
  variation := ⟨large_index_square_lift, liftRejected, liftRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨liftRejected, ?_, rfl, liftRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),⊤,sumDiff.range,?_⟩
    change ((⊤ : Submodule ℤ Plane).toAddSubgroup.index : ℤ) ≠ sumDiff.range.toAddSubgroup.index
    rw [sumDiff_index]
    change ((⊤ : AddSubgroup Plane).index : ℤ) ≠ 2
    simp
noncomputable def liftRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@large_index_square_lift) (Realization liftSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.LeeSquareCompression.large_index_square_lift.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.LeeSquareCompression.liftSource
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena⟩
  objectArena := .source ⟨liftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena ⟨liftSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize liftSignature (fun _ _ K => (K.toAddSubgroup.index : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.LeeSquareCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","domain","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev upperSignature : Signature where
  Params := ℕ × ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def upperActual : Realization upperSignature := realize upperSignature
  (fun _ p k => (p.1 : ℤ)^2*k) (fun e => nomatch e)
noncomputable def upperRejected : Realization upperSignature := realize upperSignature
  (fun _ _ _ => 1000) (fun e => nomatch e)
abbrev upperArena : Arena where
  signature := upperSignature
  Law R := ∀ {c k : ℕ} {s : ℤ} (_ : 2 ≤ c) (_ : 1 ≤ k) (_ : 3 ≤ s) (a b : Target c k)
    (_ : ∀ g : Target c k, ∃ x y : ℤ, |x|+|y| ≤ s ∧ x • a+y • b = g),
    R.readout () (c,s) k ≤ 2*s^2 ∨
      (Odd (c : ℤ) ∧ (c : ℤ) ∣ 2*s+1 ∧
        2*R.readout () (c,s) k ≤ (2*s+1)^2-(c : ℤ)^2)
private theorem upperRejected_law : ¬ upperArena.Law upperRejected := by
  intro h
  have hh := h (c := 2) (k := 1) (s := 3) (by decide) (by decide) (by decide)
    (1,0) (0,1) small_cover
  norm_num [upperRejected,realize] at hh
noncomputable def upperSource : Registration upperArena (type_of% (@arbitrary_pair_upper_bound)) where
  actual := upperActual
  bridge := Iff.rfl
  variation := ⟨arbitrary_pair_upper_bound, upperRejected, upperRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨upperRejected, ?_, rfl, upperRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(2,3),0,1,by norm_num [upperActual,realize]⟩
noncomputable def upperRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@arbitrary_pair_upper_bound) (Realization upperSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.LeeSquareCompression.arbitrary_pair_upper_bound.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.LeeSquareCompression.upperSource
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena⟩
  objectArena := .source ⟨upperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena ⟨upperSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize upperSignature (fun _ p k => (p.1 : ℤ)^2*k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.LeeSquareCompression
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev latticeArena : Arena where
  signature := liftSignature
  Law R := ∀ (K : Submodule ℤ Plane) {c s : ℤ} (_ : 2 ≤ c) (_ : 3 ≤ s)
    (_ : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1)
    (_ : ∀ z : Plane, ∃ r : Plane, |r 0|+|r 1| ≤ s ∧ z-r ∈ K),
    R.readout () () K ≤ 2*s^2 ∨
      (Odd c ∧ c ∣ 2*s+1 ∧ 2*R.readout () () K ≤ (2*s+1)^2-c^2)
private theorem latticeRejected_law : ¬ latticeArena.Law liftRejected := by
  intro h
  have hh := h (grid 3) (c := 3) (s := 3) (by norm_num) (by norm_num)
    (fun _ hz => grid_div 3 hz) (by
      intro z
      obtain ⟨r,hr,hmem⟩ := grid_cover 1 z
      exact ⟨r, by norm_num at hr ⊢; omega, hmem⟩)
  norm_num [liftRejected,realize] at hh
noncomputable def latticeSource : Registration latticeArena (type_of% (@lattice_upper_bound)) where
  actual := liftActual
  bridge := Iff.rfl
  variation := ⟨lattice_upper_bound, liftRejected, latticeRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨liftRejected, ?_, rfl, latticeRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := liftSource.dependence
noncomputable def latticeRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@lattice_upper_bound) (Realization liftSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.LeeSquareCompression.lattice_upper_bound.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.LeeSquareCompression.latticeSource
  realizationSource := none
  generated := false
  arena := .source ⟨latticeArena⟩
  objectArena := .source ⟨latticeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source latticeArena ⟨latticeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize liftSignature
    (fun _ _ K => (K.toAddSubgroup.index : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.LeeSquareCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.LeeSquareCompression
