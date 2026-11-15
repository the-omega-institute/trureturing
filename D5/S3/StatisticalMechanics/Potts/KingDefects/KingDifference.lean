/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingDifference
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Klein-valued discrete integration and rainbow-block rigidity on rectangles. -/
/-
admission_basis: escape-witness
escape_witness: integrate_v (propagation of a cocycle along an arbitrary row),
  integrationEquiv (root and difference field reconstruct a unique colouring),
  horizontal_slot_eq and vertical_slot_eq (rainbow rigidity along clear intervals).
K: proof_shape=bind-only; consumers=DiffField,KingDiagonal.DiagonalSlots,KingDiagonal.OrderedPair,KingDiagonal.klein_alphabet,KingDiagonal.klein_zero,KingDiagonal.normalized_recover,KingDiagonal.normalized_valid,KingDiagonal.slot_raw,KingHorizontal.BoundaryData,KingHorizontal.InteriorAlphabet,KingHorizontal.NZPair,KingHorizontal.OrdinaryAlphabet,KingHorizontal.SupportAlphabet,KingHorizontal.boundary_word_map_injective,KingHorizontal.boundary_word_map_surjective,KingHorizontal.coded_boundary,KingHorizontal.coded_boundary_valid,KingHorizontal.lower_pair_values,KingHorizontal.ordinary_value,KingHorizontal.row_reflect_differentiate,KingHorizontal.row_reflect_raw,KingHorizontal.support_alphabet_card,Rainbow,add_add_cancel,add_eq_zero,colourEquiv,count_fixed_edge,defectIntegrationEquiv,difference_unique,differentiate,differentiate_cocycle,differentiate_edgeValue,differentiate_integrate,edgeValue,good_differentiate,integrate,integrate_differentiate,integrate_h,integrate_root,integrate_v,integrationEquiv,neg_self,rainbow_algebra,rainbow_block,raw_differentiate_iff,relabelDefectEquiv,rootZeroEquiv,self_add
colourEquiv: proof_shape=bind-only; consumers=relabelDefectEquiv
neg_self: proof_shape=bind-only; consumers=add_eq_zero
self_add: proof_shape=bind-only; consumers=add_add_cancel
add_add_cancel: proof_shape=bind-only; consumers=integrate_h
add_eq_zero: proof_shape=bind-only; consumers=rainbow_algebra,raw_differentiate_iff
DiffField: proof_shape=bind-only; consumers=Cocycle,GoodBlock,KingDiagonal.diagonalSlotEquiv,KingDiagonal.extractSlots,KingDiagonal.extract_valid,KingDiagonal.raw_h_ordinary,KingDiagonal.raw_h_special,KingDiagonal.raw_v_ordinary,KingDiagonal.raw_v_special,KingDiagonal.slotField,KingDiagonal.slot_good,KingDiagonal.slot_raw,KingDiagonal.slot_reconstruction,KingDiagonal.slot_special,KingDiagonal.special_block,KingHorizontal.CutFields,KingHorizontal.bottom_edge_value,KingHorizontal.bottom_field,KingHorizontal.bottom_field_join,KingHorizontal.bottom_field_raw,KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_bottom_slot_equiv,KingHorizontal.boundary_build,KingHorizontal.boundary_build_raw,KingHorizontal.boundary_extract,KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_h,KingHorizontal.boundary_reconstruct,KingHorizontal.boundary_slot_equiv,KingHorizontal.boundary_top_shared,KingHorizontal.boundary_v,KingHorizontal.boundary_word_equiv,KingHorizontal.horizontal_cut_equiv,KingHorizontal.interior_slot_equiv,KingHorizontal.join_field,KingHorizontal.join_restrict,KingHorizontal.raw_of_halves,KingHorizontal.row_reflect,KingHorizontal.row_reflect_differentiate,KingHorizontal.row_reflect_equiv,KingHorizontal.row_reflect_raw,KingHorizontal.top_edge_value,KingHorizontal.top_field,KingHorizontal.top_field_join,KingHorizontal.top_field_raw,N_e,RawAdmissible,defectIntegrationEquiv,difference_unique,differentiate,differentiate_integrate,edgeValue,goodBlock_of_raw,horizontal_slot_eq,integrate,integrate_h,integrate_root,integrate_v,integrationEquiv,rainbow_block,rainbow_field,rootZeroEquiv,vertical_slot_eq
Cocycle: proof_shape=bind-only; consumers=KingHorizontal.boundary_build_raw,RawAdmissible,differentiate_cocycle,differentiate_integrate,integrate_v,integrationEquiv,rainbow_field
differentiate: proof_shape=bind-only; consumers=KingHorizontal.row_reflect_differentiate,defectIntegrationEquiv,difference_unique,differentiate_cocycle,differentiate_edgeValue,differentiate_integrate,good_differentiate,integrate_differentiate,integrate_h,integrate_v,integrationEquiv,rainbow_block,raw_differentiate_iff,rootZeroEquiv
differentiate_cocycle: proof_shape=bind-only; consumers=integrate_differentiate,integrationEquiv,raw_differentiate_iff
integrate: proof_shape=bind-only; consumers=KingHorizontal.row_reflect_raw,defectIntegrationEquiv,differentiate_integrate,integrate_differentiate,integrate_h,integrate_root,integrate_v,integrationEquiv,rainbow_field,rootZeroEquiv
integrate_root: proof_shape=bind-only; consumers=defectIntegrationEquiv,integrate_differentiate,integrationEquiv,rootZeroEquiv
integrate_h: proof_shape=bind-only; consumers=differentiate_integrate
integrate_v: proof_shape=content; consumers=differentiate_integrate
differentiate_integrate: proof_shape=content; consumers=KingHorizontal.row_reflect_raw,defectIntegrationEquiv,integrate_differentiate,integrationEquiv,rainbow_field,rootZeroEquiv
difference_unique: proof_shape=content; consumers=integrate_differentiate
integrate_differentiate: proof_shape=bind-only; consumers=integrationEquiv,rootZeroEquiv
integrationEquiv: proof_shape=content; consumers=defectIntegrationEquiv
edgeValue: proof_shape=bind-only; consumers=KingDiagonal.slot_raw,KingDiagonal.special_block,KingHorizontal.bottom_edge_value,KingHorizontal.boundary_build_raw,KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_h,KingHorizontal.top_edge_value,RawAdmissible,differentiate_edgeValue,goodBlock_of_raw
RawAdmissible: proof_shape=bind-only; consumers=KingDiagonal.diagonalSlotEquiv,KingDiagonal.extract_valid,KingDiagonal.raw_h_ordinary,KingDiagonal.raw_h_special,KingDiagonal.raw_v_ordinary,KingDiagonal.raw_v_special,KingDiagonal.slot_raw,KingDiagonal.slot_reconstruction,KingDiagonal.special_block,KingHorizontal.CutFields,KingHorizontal.bottom_field_raw,KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_bottom_slot_equiv,KingHorizontal.boundary_build_raw,KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_h,KingHorizontal.boundary_reconstruct,KingHorizontal.boundary_slot_equiv,KingHorizontal.boundary_top_shared,KingHorizontal.boundary_v,KingHorizontal.boundary_word_equiv,KingHorizontal.horizontal_cut_equiv,KingHorizontal.interior_slot_equiv,KingHorizontal.raw_of_halves,KingHorizontal.row_reflect_equiv,KingHorizontal.row_reflect_raw,KingHorizontal.top_field_raw,N_e,defectIntegrationEquiv,goodBlock_of_raw,horizontal_slot_eq,raw_differentiate_iff,rootZeroEquiv,vertical_slot_eq
differentiate_edgeValue: proof_shape=bind-only; consumers=raw_differentiate_iff
raw_differentiate_iff: proof_shape=bind-only; consumers=KingHorizontal.row_reflect_raw,defectIntegrationEquiv,rootZeroEquiv
defectIntegrationEquiv: proof_shape=content; consumers=KingHorizontal.row_reflect_raw,count_fixed_edge,rootZeroEquiv
rootZeroEquiv: proof_shape=content; consumers=none
N_e: proof_shape=bind-only; consumers=KingDiagonal.N_D_two_columns,KingDiagonal.N_D_two_rows,KingDiagonal.diagonal_count,KingHorizontal.boundary_count,KingHorizontal.boundary_count_at,KingHorizontal.boundary_count_pos,KingHorizontal.boundary_count_zero,KingHorizontal.boundary_one_column,KingHorizontal.boundary_row_sum,KingHorizontal.boundary_rows_count,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.horizontal_sum,KingHorizontal.horizontal_three_rows,KingHorizontal.horizontal_two_columns,KingHorizontal.horizontal_two_rows,KingHorizontal.interior_count,KingHorizontal.interior_count_alphabets,KingHorizontal.interior_count_support,KingHorizontal.interior_one_column_count,KingHorizontal.interior_row_sum,KingHorizontal.interior_three_rows_count,N_D,N_H,N_reflect,N_transpose,count_fixed_edge,count_from_fields,fields_eq_six_canonical,sum_fields_by_kind
relabelDefectEquiv: proof_shape=bind-only; consumers=count_fixed_edge
count_fixed_edge: proof_shape=content; consumers=KingHorizontal.horizontal_count_row_reflect,N_reflect,N_transpose,count_from_fields
count_from_fields: proof_shape=content; consumers=fields_eq_six_canonical
Rainbow: proof_shape=bind-only; consumers=good_differentiate,rainbow_algebra,rainbow_block
rainbow_algebra: proof_shape=bind-only; consumers=rainbow_block
rainbow_block: proof_shape=bind-only; consumers=rainbow_field
GoodBlock: proof_shape=bind-only; consumers=good_differentiate,rainbow_field
good_differentiate: proof_shape=bind-only; consumers=rainbow_field
rainbow_field: proof_shape=bind-only; consumers=goodBlock_of_raw
BlockAvoids: proof_shape=bind-only; consumers=KingDiagonal.diagonal_clear,KingHorizontal.boundary_h,KingHorizontal.boundary_v,goodBlock_of_raw,horizontal_slot_eq,vertical_slot_eq
goodBlock_of_raw: proof_shape=bind-only; consumers=KingDiagonal.extract_valid,horizontal_slot_eq,vertical_slot_eq
horizontal_slot_eq: proof_shape=content; consumers=KingDiagonal.raw_h_ordinary,KingDiagonal.raw_h_special,KingHorizontal.boundary_h
  KingDiagonal.raw_h_special,KingHorizontal.boundary_h
vertical_slot_eq: proof_shape=content; consumers=KingDiagonal.raw_v_ordinary,KingDiagonal.raw_v_special,KingHorizontal.boundary_v
  KingDiagonal.raw_v_special,KingHorizontal.boundary_v
fields_eq_six_canonical: proof_shape=content; consumers=count_by_kind
N_transpose: proof_shape=bind-only; consumers=sum_fields_by_kind
N_reflect: proof_shape=bind-only; consumers=sum_fields_by_kind
N_H: proof_shape=bind-only; consumers=KingHorizontal.horizontal_sum,KingHorizontal.horizontal_three_rows,KingHorizontal.horizontal_two_columns,KingHorizontal.horizontal_two_rows,count_by_kind,sum_fields_by_kind
N_D: proof_shape=bind-only; consumers=KingDiagonal.N_D_closed,KingDiagonal.N_D_two_columns,KingDiagonal.N_D_two_rows,count_by_kind,sum_fields_by_kind
sum_fields_by_kind: proof_shape=bind-only; consumers=count_by_kind
count_by_kind: proof_shape=content; consumers=KingClosedForm.closed_form,KingClosedForm.width_three,KingClosedForm.width_two
  KingClosedForm.width_two,KingClosedForm.width_three
The finite Klein identities support uniform structural theorems; no bounded
colouring enumeration or numerical instance is asserted.
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Algebra.BigOperators.Fin

/-! Discrete derivatives, exact integration and local rainbow rigidity. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference

open KingGrid

abbrev K := ZMod 2 × ZMod 2

private noncomputable def colourEquiv : Fin 4 ≃ K :=
  Fintype.equivOfCardEq (by simp [K])

private theorem neg_self (a : K) : -a = a := by
  exact IsAddKleinFour.neg_eq_self a

@[simp] private theorem self_add (a : K) : a + a = 0 := by
  exact IsAddKleinFour.add_self a

@[simp] private theorem add_add_cancel (a b : K) : a + (a + b) = b := by
  rw [← add_assoc, self_add, zero_add]

@[simp] private theorem add_eq_zero (a b : K) : a + b = 0 ↔ a = b := by
  simpa only [neg_self] using (add_eq_zero_iff_eq_neg (a := a) (b := b))

/-- A rectangle with `N` vertical steps and `M` horizontal steps has `(N+1)(M+1)` cells. -/
@[ext] structure DiffField (N M : ℕ) where
  h : Fin (N + 1) → Fin M → K
  v : Fin N → Fin (M + 1) → K
  deriving DecidableEq, Fintype

/-- The two paths across every elementary square have equal differences. -/
def Cocycle {N M : ℕ} (s : DiffField N M) : Prop :=
  ∀ i j, s.h i.castSucc j + s.v i j.succ =
    s.v i j.castSucc + s.h i.succ j

def differentiate {N M : ℕ} (f : Cell (N + 1) (M + 1) → K) : DiffField N M where
  h i j := f (i,j.castSucc) + f (i,j.succ)
  v i j := f (i.castSucc,j) + f (i.succ,j)

private theorem differentiate_cocycle {N M : ℕ} (f : Cell (N + 1) (M + 1) → K) :
    Cocycle (differentiate f) := by
  intro i j
  dsimp [differentiate]
  have reorder (a b c d : K) : (a + b)+(b + d) = (a + c)+(c + d) := by
    simp [add_assoc, ← add_assoc b b, ← add_assoc c c]
  exact reorder _ _ _ _

def integrate {N M : ℕ} (t : K) (s : DiffField N M) : Cell (N + 1) (M + 1) → K :=
  fun p => t + Fin.partialSum (fun i => s.v i 0) p.1 + Fin.partialSum (s.h p.1) p.2

private theorem integrate_root {N M : ℕ} (t : K) (s : DiffField N M) :
    integrate t s (0, 0) = t := by simp [integrate]

private theorem integrate_h {N M : ℕ} (t : K) (s : DiffField N M)
    (i : Fin (N + 1)) (j : Fin M) :
    (differentiate (integrate t s)).h i j = s.h i j := by
  dsimp [differentiate, integrate]
  rw [Fin.partialSum_succ]
  simpa only [add_assoc] using add_add_cancel
    (t + Fin.partialSum (fun i => s.v i 0) i + Fin.partialSum (s.h i) j.castSucc) (s.h i j)

private theorem integrate_v {N M : ℕ} (t : K) (s : DiffField N M) (hs : Cocycle s)
    (i : Fin N) (j : Fin (M + 1)) :
    (differentiate (integrate t s)).v i j = s.v i j := by
  induction j using Fin.inductionOn with
  | zero =>
    dsimp [differentiate, integrate]
    rw [Fin.partialSum_succ]
    simp [add_left_comm, add_comm]
  | succ j ih =>
    have hc := hs i j
    have hd : (differentiate (integrate t s)).v i j.succ =
        (differentiate (integrate t s)).v i j.castSucc +
          (s.h i.castSucc j + s.h i.succ j) := by
      dsimp [differentiate, integrate]
      simp only [Fin.partialSum_succ]
      abel
    rw [hd, ih]
    have hc' := congrArg (fun z => s.h i.castSucc j + z) hc
    simpa [add_assoc, add_left_comm, add_comm] using hc'.symm

theorem differentiate_integrate {N M : ℕ} (t : K) (s : DiffField N M)
    (hs : Cocycle s) : differentiate (integrate t s) = s := by
  apply DiffField.ext
  · funext i j
    exact integrate_h t s i j
  · funext i j
    exact integrate_v t s hs i j

private theorem difference_unique {N M : ℕ} (f g : Cell (N + 1) (M + 1) → K)
    (hr : f (0, 0) = g (0, 0)) (hd : differentiate f = differentiate g) : f = g := by
  have base (i : Fin (N + 1)) : f (i,0) = g (i,0) := by
    induction i using Fin.inductionOn with
    | zero => exact hr
    | succ i ih =>
      have hv := congrFun (congrFun (congrArg DiffField.v hd) i) 0
      change f (i.castSucc,0) + f (i.succ,0) = g (i.castSucc,0) + g (i.succ,0) at hv
      rw [ih] at hv
      exact add_left_cancel hv
  funext p
  obtain ⟨i,j⟩ := p
  induction j using Fin.inductionOn with
  | zero => exact base i
  | succ j ih =>
    have hh := congrFun (congrFun (congrArg DiffField.h hd) i) j
    change f (i,j.castSucc) + f (i,j.succ) = g (i,j.castSucc) + g (i,j.succ) at hh
    rw [ih] at hh
    exact add_left_cancel hh

private theorem integrate_differentiate {N M : ℕ} (f : Cell (N + 1) (M + 1) → K) :
    integrate (f (0, 0)) (differentiate f) = f :=
  difference_unique _ _ (integrate_root _ _)
    (differentiate_integrate _ _ (differentiate_cocycle f))

/-- No defect restriction is needed for discrete integration. -/
private def integrationEquiv (N M : ℕ) :
    (Cell (N + 1) (M + 1) → K) ≃ K × {s : DiffField N M // Cocycle s} where
  toFun f := (f (0, 0), ⟨differentiate f, differentiate_cocycle f⟩)
  invFun q := integrate q.1 q.2.val
  left_inv := integrate_differentiate
  right_inv q := by
    apply Prod.ext (integrate_root _ _)
    exact Subtype.ext (differentiate_integrate _ _ q.2.property)


def edgeValue {N M : ℕ} (s : DiffField N M) : Edge (N + 1) (M + 1) → K
  | .H i j => s.h i j
  | .V i j => s.v i j
  | .D i j => s.h i.castSucc j + s.v i j.succ
  | .A i j => s.h i.castSucc j + s.v i j.castSucc

def RawAdmissible {N M : ℕ} (e : Edge (N + 1) (M + 1)) (s : DiffField N M) : Prop :=
  Cocycle s ∧ ∀ d, edgeValue s d = 0 ↔ d = e

private theorem differentiate_edgeValue {N M : ℕ} (f : Cell (N + 1) (M + 1) → K)
    (e : Edge (N + 1) (M + 1)) :
    edgeValue (differentiate f) e = f (end0 e) + f (end1 e) := by
  cases e with
  | H i j => rfl
  | V i j => rfl
  | D i j =>
    change (f (i.castSucc,j.castSucc) + f (i.castSucc,j.succ)) +
      (f (i.castSucc,j.succ) + f (i.succ,j.succ)) = _
    simp [add_assoc]
    rfl
  | A i j =>
    change (f (i.castSucc,j.castSucc) + f (i.castSucc,j.succ)) +
      (f (i.castSucc,j.castSucc) + f (i.succ,j.castSucc)) = _
    simp [add_assoc, add_left_comm]
    rfl

theorem raw_differentiate_iff {N M : ℕ} (f : Cell (N + 1) (M + 1) → K)
    (e : Edge (N + 1) (M + 1)) :
    RawAdmissible e (differentiate f) ↔ DefectAt e f := by
  simp only [RawAdmissible, differentiate_cocycle, true_and,
    differentiate_edgeValue, add_eq_zero, DefectAt, mono]

def defectIntegrationEquiv {N M : ℕ} (e : Edge (N + 1) (M + 1)) :
    {f : Cell (N + 1) (M + 1) → K // DefectAt e f} ≃
      K × {s : DiffField N M // RawAdmissible e s} where
  toFun f := (f.val (0, 0), ⟨differentiate f.val,
    (raw_differentiate_iff f.val e).mpr f.property⟩)
  invFun q := ⟨integrate q.1 q.2.val, by
    apply (raw_differentiate_iff _ e).mp
    rw [differentiate_integrate _ _ q.2.property.1]
    exact q.2.property⟩
  left_inv f := Subtype.ext ((integrationEquiv N M).left_inv f.val)
  right_inv q := by
    apply Prod.ext (integrate_root _ _)
    exact Subtype.ext (differentiate_integrate _ _ q.2.property.1)

/-- The field alone parametrizes colourings whose root colour is zero. -/
private def rootZeroEquiv {N M : ℕ} (e : Edge (N + 1) (M + 1)) :
    {f : Cell (N + 1) (M + 1) → K // DefectAt e f ∧ f (0, 0) = 0} ≃
      {s : DiffField N M // RawAdmissible e s} where
  toFun f := ⟨differentiate f.val, (raw_differentiate_iff f.val e).mpr f.property.1⟩
  invFun s := ⟨integrate 0 s.val,
    (defectIntegrationEquiv e).symm (0,s) |>.property, integrate_root _ _⟩
  left_inv f := by
    apply Subtype.ext
    simpa only [f.property.2] using integrate_differentiate f.val
  right_inv s := Subtype.ext (differentiate_integrate _ _ s.property.1)

/-- By `rootZeroEquiv`, this is also the count of maps with defect `e` and root zero. -/
noncomputable def N_e {N M : ℕ} (e : Edge (N + 1) (M + 1)) : ℕ :=
  Nat.card {s : DiffField N M // RawAdmissible e s}

private noncomputable def relabelDefectEquiv {n k : ℕ} (e : Edge n k) :
    {f : Cell n k → Fin 4 // DefectAt e f} ≃
      {f : Cell n k → K // DefectAt e f} where
  toFun f := ⟨colourEquiv ∘ f.val, by
    intro d
    simpa only [mono, Function.comp_apply, colourEquiv.injective.eq_iff] using f.property d⟩
  invFun f := ⟨colourEquiv.symm ∘ f.val, by
    intro d
    simpa only [mono, Function.comp_apply, colourEquiv.symm.injective.eq_iff] using f.property d⟩
  left_inv f := by apply Subtype.ext; funext p; exact colourEquiv.symm_apply_apply _
  right_inv f := by apply Subtype.ext; funext p; exact colourEquiv.apply_symm_apply _

theorem count_fixed_edge {N M : ℕ} (e : Edge (N + 1) (M + 1)) :
    Nat.card {f : Cell (N + 1) (M + 1) → Fin 4 // DefectAt e f} = 4 * N_e e := by
  rw [Nat.card_congr (relabelDefectEquiv e),
    Nat.card_congr (defectIntegrationEquiv e), Nat.card_prod]
  simp [K, N_e, Nat.card_eq_fintype_card]

private theorem count_from_fields (N M : ℕ) :
    L (N + 1) (M + 1) = 4 * ∑ e : Edge (N + 1) (M + 1), N_e e := by
  rw [count_by_edge]
  simp_rw [count_fixed_edge]
  exact (Finset.mul_sum ..).symm

/-- The six pairs of the four vertices of a square. -/
private def Rainbow (a b c d : K) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

private theorem rainbow_algebra (a b c d : K) :
    Rainbow a b c d ↔
      a + b = c + d ∧ a + c = b + d ∧ a + b ≠ 0 ∧ a + c ≠ 0 ∧ a + b ≠ a + c := by
  constructor
  · rintro ⟨hab,hac,had,hbc,hbd,hcd⟩
    have hx : a + b ≠ 0 := fun h => hab ((add_eq_zero a b).mp h)
    have hy : a + c ≠ 0 := fun h => hac ((add_eq_zero a c).mp h)
    have hz : a + d ≠ 0 := fun h => had ((add_eq_zero a d).mp h)
    have hxy : a + b ≠ a + c := fun h => hbc (add_left_cancel h)
    have hzx : a + d ≠ a + b := fun h => hbd (add_left_cancel h).symm
    have hzy : a + d ≠ a + c := fun h => hcd (add_left_cancel h).symm
    have ht := IsAddKleinFour.eq_add_of_ne_all hx hy hxy hz hzx hzy
    have hd : d = a + (b + c) := by
      simpa [add_assoc, add_left_comm, add_comm] using congrArg (fun z => a + z) ht
    subst d
    refine ⟨?_,?_,hx,hy,hxy⟩ <;> simp [add_left_comm]
  · rintro ⟨hh,_,hx,hy,hxy⟩
    have hd : d = a + (b + c) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        (congrArg (fun z => c + z) hh).symm
    subst d
    have hab : a ≠ b := fun h => hx ((add_eq_zero a b).mpr h)
    have hac : a ≠ c := fun h => hy ((add_eq_zero a c).mpr h)
    have hbc : b ≠ c := fun h => hxy (congrArg (fun z => a + z) h)
    refine ⟨hab,hac,?_,hbc,?_,?_⟩
    · intro h
      have hz : b + c = 0 := add_left_cancel
        (show a + (b + c) = a + 0 by simpa only [add_zero] using h.symm)
      exact hbc ((add_eq_zero b c).mp hz)
    · intro h
      have hz : a + c = 0 := by
        simpa [add_assoc, add_left_comm, add_comm] using
          (congrArg (fun z => b + z) h).symm
      exact hy hz
    · intro h
      have hz : a + b = 0 := by
        simpa [add_assoc, add_left_comm, add_comm] using
          (congrArg (fun z => c + z) h).symm
      exact hx hz

/-- Rainbow squares have constant opposite slots and distinct nonzero directions. -/
private theorem rainbow_block {N M : ℕ} (f : Cell (N + 1) (M + 1) → K)
    (i : Fin N) (j : Fin M) :
    Rainbow (f (i.castSucc,j.castSucc)) (f (i.castSucc,j.succ))
      (f (i.succ,j.castSucc)) (f (i.succ,j.succ)) ↔
      (differentiate f).h i.castSucc j = (differentiate f).h i.succ j ∧
      (differentiate f).v i j.castSucc = (differentiate f).v i j.succ ∧
      (differentiate f).h i.castSucc j ≠ 0 ∧
      (differentiate f).v i j.castSucc ≠ 0 ∧
      (differentiate f).h i.castSucc j ≠ (differentiate f).v i j.castSucc := by
  exact rainbow_algebra _ _ _ _


/-- All six bonds of an elementary block have nonzero difference. -/
private def GoodBlock {N M : ℕ} (s : DiffField N M) (i : Fin N) (j : Fin M) : Prop :=
  s.h i.castSucc j ≠ 0 ∧ s.v i j.castSucc ≠ 0 ∧
    s.h i.castSucc j + s.v i j.succ ≠ 0 ∧
    s.h i.castSucc j + s.v i j.castSucc ≠ 0 ∧
    s.v i j.succ ≠ 0 ∧ s.h i.succ j ≠ 0

private theorem good_differentiate {N M : ℕ} (f : Cell (N + 1) (M + 1) → K)
    (i : Fin N) (j : Fin M) :
    GoodBlock (differentiate f) i j ↔
      Rainbow (f (i.castSucc,j.castSucc)) (f (i.castSucc,j.succ))
        (f (i.succ,j.castSucc)) (f (i.succ,j.succ)) := by
  simp [GoodBlock, Rainbow, differentiate, add_assoc, add_left_comm]

/-- A cocycle has a good block exactly when its opposite slots agree. -/
private theorem rainbow_field {N M : ℕ} (s : DiffField N M) (hs : Cocycle s)
    (i : Fin N) (j : Fin M) :
    GoodBlock s i j ↔
      s.h i.castSucc j = s.h i.succ j ∧ s.v i j.castSucc = s.v i j.succ ∧
      s.h i.castSucc j ≠ 0 ∧ s.v i j.castSucc ≠ 0 ∧
      s.h i.castSucc j ≠ s.v i j.castSucc := by
  have h := (good_differentiate (integrate 0 s) i j).trans
    (rainbow_block (integrate 0 s) i j)
  simpa only [differentiate_integrate 0 s hs] using h

/-- The selected edge is absent from the six bonds of a block. -/
def BlockAvoids {N M : ℕ} (e : Edge (N + 1) (M + 1)) (i : Fin N) (j : Fin M) : Prop :=
  (Edge.H i.castSucc j : Edge (N + 1) (M + 1)) ≠ e ∧
    (Edge.V i j.castSucc : Edge (N + 1) (M + 1)) ≠ e ∧
    (Edge.D i j : Edge (N + 1) (M + 1)) ≠ e ∧
    (Edge.A i j : Edge (N + 1) (M + 1)) ≠ e ∧
    (Edge.V i j.succ : Edge (N + 1) (M + 1)) ≠ e ∧
    (Edge.H i.succ j : Edge (N + 1) (M + 1)) ≠ e

/-- Every block missing the selected edge has constant opposite differences. -/
theorem goodBlock_of_raw {N M : ℕ} (e : Edge (N + 1) (M + 1))
    (s : DiffField N M) (hs : RawAdmissible e s) (i : Fin N) (j : Fin M)
    (havoid : BlockAvoids e i j) :
    s.h i.castSucc j = s.h i.succ j ∧ s.v i j.castSucc = s.v i j.succ ∧
      s.h i.castSucc j ≠ 0 ∧ s.v i j.castSucc ≠ 0 ∧
      s.h i.castSucc j ≠ s.v i j.castSucc := by
  apply (rainbow_field s hs.1 i j).mp
  have nz (d : Edge (N + 1) (M + 1)) (hne : d ≠ e) : edgeValue s d ≠ 0 :=
    mt (hs.2 d).mp hne
  obtain ⟨ht,hl,hd,ha,hr,hb⟩ := havoid
  exact ⟨nz (.H i.castSucc j) ht, nz (.V i j.castSucc) hl, nz (.D i j) hd,
    nz (.A i j) ha, nz (.V i j.succ) hr, nz (.H i.succ j) hb⟩

/-- A horizontal slot is constant across any interval of unaffected blocks. -/
theorem horizontal_slot_eq {N M : ℕ} (e : Edge (N + 1) (M + 1))
    (s : DiffField N M) (hs : RawAdmissible e s) (j : Fin M)
    (a b : Fin (N + 1)) (hab : a ≤ b)
    (hclear : ∀ i : Fin N, a.val ≤ i.val → i.val < b.val → BlockAvoids e i j) :
    s.h a j = s.h b j := by
  revert hab hclear
  induction b using Fin.inductionOn with
  | zero =>
    intro hab _
    have ha : a = 0 := by apply Fin.ext; simp_all
    subst a
    rfl
  | succ b ih =>
    intro hab hclear
    by_cases heq : a = b.succ
    · rw [heq]
    have ha : a ≤ b.castSucc := by
      simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ] at *
      have hne : a.val ≠ b.val + 1 := fun h => heq (Fin.ext h)
      omega
    calc
      s.h a j = s.h b.castSucc j := ih ha (fun i hia hib => hclear i hia (by
        simp only [Fin.val_castSucc] at hib
        simp only [Fin.val_succ]
        omega))
      _ = s.h b.succ j := (goodBlock_of_raw e s hs b j
        (hclear b ha (by simp))).1

/-- A vertical slot is constant across any interval of unaffected blocks. -/
theorem vertical_slot_eq {N M : ℕ} (e : Edge (N + 1) (M + 1))
    (s : DiffField N M) (hs : RawAdmissible e s) (i : Fin N)
    (a b : Fin (M + 1)) (hab : a ≤ b)
    (hclear : ∀ j : Fin M, a.val ≤ j.val → j.val < b.val → BlockAvoids e i j) :
    s.v i a = s.v i b := by
  revert hab hclear
  induction b using Fin.inductionOn with
  | zero =>
    intro hab _
    have ha : a = 0 := by apply Fin.ext; simp_all
    subst a
    rfl
  | succ b ih =>
    intro hab hclear
    by_cases heq : a = b.succ
    · rw [heq]
    have ha : a ≤ b.castSucc := by
      simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ] at *
      have hne : a.val ≠ b.val + 1 := fun h => heq (Fin.ext h)
      omega
    calc
      s.v i a = s.v i b.castSucc := ih ha (fun j hja hjb => hclear j hja (by
        simp only [Fin.val_castSucc] at hjb
        simp only [Fin.val_succ]
        omega))
      _ = s.v i b.succ := (goodBlock_of_raw e s hs i b
        (hclear b ha (by simp))).2.1

/-- The canonical count is one sixth of the total root-zero field count. -/
private theorem fields_eq_six_canonical (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    (∑ e : Edge (N + 1) (M + 1), N_e e) = 6 * T (N + 1) (M + 1) := by
  have h := labelled_eq_twentyFour (N + 1) (M + 1) (by omega) (by omega)
  rw [count_from_fields] at h
  have he : 24 * T (N + 1) (M + 1) = 4 * (6 * T (N + 1) (M + 1)) := by omega
  rw [he] at h
  exact Nat.mul_left_cancel (by norm_num : 0 < 4) h


private theorem N_transpose {N M : ℕ} (e : Edge (N + 1) (M + 1)) :
    N_e (transposeEdge e) = N_e e := by
  have h := Nat.card_congr (transposeDefectEquiv (C := Fin 4) e)
  rw [count_fixed_edge, count_fixed_edge] at h
  exact Nat.mul_left_cancel (by norm_num : 0 < 4) h.symm

private theorem N_reflect {N M : ℕ} (e : Edge (N + 1) (M + 1)) :
    N_e (reflectEdge e) = N_e e := by
  have h := Nat.card_congr (reflectDefectEquiv (C := Fin 4) e)
  rw [count_fixed_edge, count_fixed_edge] at h
  exact Nat.mul_left_cancel (by norm_num : 0 < 4) h.symm

/-- Sum of root-zero counts over horizontal defects in an `(N+1)` by `(M+1)` rectangle. -/
noncomputable def N_H (N M : ℕ) : ℕ :=
  ∑ i : Fin (N + 1), ∑ j : Fin M, N_e (.H i j : Edge (N + 1) (M + 1))

/-- Sum of root-zero counts over descending diagonals in the same rectangle. -/
noncomputable def N_D (N M : ℕ) : ℕ :=
  ∑ i : Fin N, ∑ j : Fin M, N_e (.D i j : Edge (N + 1) (M + 1))

/-- Transposition and reflection reduce the four orientations to H and D. -/
private theorem sum_fields_by_kind (N M : ℕ) :
    (∑ e : Edge (N + 1) (M + 1), N_e e) = N_H N M + N_H M N + 2 * N_D N M := by
  rw [sum_edges]
  have hV : (∑ i : Fin N, ∑ j : Fin (M + 1), N_e (.V i j : Edge (N + 1) (M + 1))) =
      N_H M N := by
    calc
      _ = ∑ i : Fin N, ∑ j : Fin (M + 1),
          N_e (.H j i : Edge (M + 1) (N + 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact (N_transpose (.V i j : Edge (N + 1) (M + 1))).symm
      _ = ∑ j : Fin (M + 1), ∑ i : Fin N,
          N_e (.H j i : Edge (M + 1) (N + 1)) := Finset.sum_comm
      _ = N_H M N := rfl
  have hA : (∑ i : Fin N, ∑ j : Fin M, N_e (.A i j : Edge (N + 1) (M + 1))) =
      N_D N M := by
    unfold N_D
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp (Fin.revPerm (n := M))
      (fun j => N_e (.A i j : Edge (N + 1) (M + 1)))]
    apply Finset.sum_congr rfl
    intro j _
    exact N_reflect (.D i j : Edge (N + 1) (M + 1))
  change N_H N M + _ + N_D N M + _ = _
  calc
    _ = N_H N M + N_H M N + N_D N M + N_D N M :=
      congrArg₂ (fun a b => N_H N M + a + N_D N M + b) hV hA
    _ = _ := by omega

/-- This is the orientation decomposition used in the closed-form count. -/
theorem count_by_kind (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    N_H N M + N_H M N + 2 * N_D N M = 6 * T (N + 1) (M + 1) := by
  rw [← sum_fields_by_kind]
  exact fields_eq_six_canonical N M hN hM

#print axioms defectIntegrationEquiv
#print axioms rootZeroEquiv
#print axioms count_from_fields
#print axioms rainbow_block
#print axioms rainbow_field
#print axioms horizontal_slot_eq
#print axioms vertical_slot_eq
#print axioms count_by_kind

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
