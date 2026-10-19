/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transport forward orbit phases under timed history equivalences. -/

/- Use the existing actual primitive paths, orbit quotient and canonical least-word basis. Offsets are forward phases; general transport laws allow every nonzero period. -/
import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import D5.S3.ConceptDynamics.Coding.CountedPositiveTriangleModThree
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.SplitTowerTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.CountedRelativeGyrationTransport
open scoped BigOperators
open CountedMatrixOverlap
open CountedOrderTypeGyration
open EssentialWordRealization
open FixedBlockRigidity.BlockCoordinates (blockAddress assemble_address shift_iterate_translate)
open StandardBeamHomeomorphisms (translate translate_zero translate_add)

/-- A genuine equivalence of the two actual legal-history carriers, with the
literal integer-time law. This packages equivariance, never a gyration identity. -/
structure TimedEquiv {n m : ℕ} (A : CountMat n n) (B : CountMat m m) where
  equiv : Path A ≃ Path B
  time : ∀ s x, equiv (translate (countedGraph A) s x) =
    translate (countedGraph B) s (equiv x)

namespace TimedEquiv
variable {n m p : ℕ} {A : CountMat n n} {B : CountMat m m} {C : CountMat p p}

def refl (A : CountMat n n) : TimedEquiv A A := ⟨Equiv.refl _,fun _ _ => rfl⟩

def comp (u : TimedEquiv A B) (v : TimedEquiv B C) : TimedEquiv A C :=
  ⟨u.equiv.trans v.equiv,fun s x =>
    (congrArg v.equiv (u.time s x)).trans (v.time s (u.equiv x))⟩

def symm (u : TimedEquiv A B) : TimedEquiv B A :=
  ⟨u.equiv.symm,by
    intro s y
    apply u.equiv.injective
    rw [u.equiv.apply_symm_apply,u.time,u.equiv.apply_symm_apply]⟩

@[ext] theorem ext {u v : TimedEquiv A B} (h : ∀ x, u.equiv x = v.equiv x) : u = v := by
  cases u with
  | mk ue ut =>
    cases v with
    | mk ve vt =>
      have he : ue = ve := Equiv.ext h
      cases he
      rfl

theorem semiconj (u : TimedEquiv A B) :
    Function.Semiconj u.equiv (shift A) (shift B) := fun x => u.time 1 x

theorem minimalPeriod (u : TimedEquiv A B) (x : Path A) :
    Function.minimalPeriod (shift B) (u.equiv x) = Function.minimalPeriod (shift A) x := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro k
  constructor
  · intro hk
    apply u.equiv.injective
    exact ((u.semiconj.iterate_right k) x).trans hk
  · intro hk
    exact ((u.semiconj.iterate_right k) x).symm.trans (congrArg u.equiv hk)


def primitiveEquiv (u : TimedEquiv A B) (d : ℕ) : PrimitivePath A d ≃ PrimitivePath B d where
  toFun x := ⟨u.equiv x.val,(u.minimalPeriod x.val).trans x.property⟩
  invFun y := ⟨u.equiv.symm y.val,by
    have h := u.minimalPeriod (u.equiv.symm y.val)
    rw [u.equiv.apply_symm_apply,y.property] at h
    exact h.symm⟩
  left_inv x := Subtype.ext (u.equiv.symm_apply_apply x.val)
  right_inv y := Subtype.ext (u.equiv.apply_symm_apply y.val)

/-- Agreement on the actual primitive histories gives equality of their
primitive images, including the original target history, by subtype extensionality. -/
theorem primitiveEquiv_congr (u v : TimedEquiv A B) {d : ℕ}
    (h : ∀ x : PrimitivePath A d, u.equiv x.val = v.equiv x.val)
    (x : PrimitivePath A d) : u.primitiveEquiv d x = v.primitiveEquiv d x := by
  apply Subtype.ext
  exact h x

theorem sameOrbit_iff (u : TimedEquiv A B) {d : ℕ} (x y : PrimitivePath A d) :
    SamePathOrbit (u.primitiveEquiv d x) (u.primitiveEquiv d y) ↔ SamePathOrbit x y := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,u.equiv.injective ?_⟩
    exact ((u.semiconj.iterate_right k) x.val).trans hk
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    exact ((u.semiconj.iterate_right k) x.val).symm.trans (congrArg u.equiv hk)

def orbitEquiv (u : TimedEquiv A B) (d : ℕ) [NeZero d] :
    ActualPathOrbit A d ≃ ActualPathOrbit B d where
  toFun := Quotient.map (u.primitiveEquiv d) (fun x y h => (u.sameOrbit_iff x y).mpr h)
  invFun := Quotient.map (u.primitiveEquiv d).symm (by
    intro x y h
    change SamePathOrbit x y at h
    change SamePathOrbit ((u.primitiveEquiv d).symm x) ((u.primitiveEquiv d).symm y)
    apply (u.sameOrbit_iff _ _).mp
    simpa only [Equiv.apply_symm_apply] using h)
  left_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    change Quotient.mk _ ((u.primitiveEquiv d).symm (u.primitiveEquiv d x)) = _
    rw [Equiv.symm_apply_apply]
  right_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    change Quotient.mk _ (u.primitiveEquiv d ((u.primitiveEquiv d).symm x)) = _
    rw [Equiv.apply_symm_apply]

/-- Exactly the actual orbit bijection, expressed in the supplier's finite
canonical bases. Its target is not chosen independently of the actual map. -/
def basisEquiv (u : TimedEquiv A B) (d : ℕ) [NeZero d] : PathBasis A d ≃ PathBasis B d :=
  (orbitBasisEquiv A).symm.trans ((u.orbitEquiv d).trans (orbitBasisEquiv B))

theorem basisEquiv_apply (u : TimedEquiv A B) {d : ℕ} [NeZero d] (b : PathBasis A d) :
    u.basisEquiv d b = canonicalPath (u.primitiveEquiv d b.val) := rfl

theorem basisEquiv_comp (u : TimedEquiv A B) (v : TimedEquiv B C)
    {d : ℕ} [NeZero d] (b : PathBasis A d) :
    (u.comp v).basisEquiv d b = v.basisEquiv d (u.basisEquiv d b) := by
  change canonicalPath (v.primitiveEquiv d (u.primitiveEquiv d b.val)) =
    canonicalPath (v.primitiveEquiv d (canonicalPath (u.primitiveEquiv d b.val)).val)
  apply canonicalPath_eq_of_sameOrbit
  exact (v.sameOrbit_iff _ _).mpr (canonicalPath_sameOrbit (u.primitiveEquiv d b.val))

def offsetFin (u : TimedEquiv A B) {d : ℕ} [NeZero d] (b : PathBasis A d) : Fin d :=
  canonicalForwardOffset (u.primitiveEquiv d b.val)

def offset (u : TimedEquiv A B) {d : ℕ} [NeZero d] (b : PathBasis A d) : ZMod d :=
  ZMod.finEquiv d (u.offsetFin b)

/-- Both offsets use the identical canonical SOURCE basis representative.
Equality of the actual primitive target images identifies their canonical
forward offsets; equality of orbit permutations alone would not suffice. -/
theorem offset_congr (u v : TimedEquiv A B) {d : ℕ} [NeZero d]
    (h : ∀ x : PrimitivePath A d, u.equiv x.val = v.equiv x.val)
    (b : PathBasis A d) : u.offset b = v.offset b := by
  change ZMod.finEquiv d (canonicalForwardOffset (u.primitiveEquiv d b.val)) =
    ZMod.finEquiv d (canonicalForwardOffset (v.primitiveEquiv d b.val))
  rw [primitiveEquiv_congr u v h b.val]

def phaseInteger (u : TimedEquiv A B) {d : ℕ} [NeZero d] (b : PathBasis A d) : ℤ :=
  (u.offsetFin b).val

theorem phase_equation (u : TimedEquiv A B) {d : ℕ} [NeZero d] (b : PathBasis A d) :
    u.equiv b.val.val = translate (countedGraph B) (u.phaseInteger b)
      (u.basisEquiv d b).val.val := by
  rw [show translate (countedGraph B) (u.phaseInteger b) (u.basisEquiv d b).val.val =
    (shift B)^[(u.offsetFin b).val] (u.basisEquiv d b).val.val from
      (shift_iterate_translate (countedGraph B) _ _).symm]
  exact canonicalForwardOffset_equation (u.primitiveEquiv d b.val)

/-- Reduce an arbitrary SIGNED integer, using Euclidean blockAddress, not a
homomorphism from all rationals or an unstated orientation convention. -/
theorem finEquiv_timeIndex {d : ℕ} [NeZero d] (s : ℤ) :
    ZMod.finEquiv d (timeIndex (d := d) s) = (s : ZMod d) := by
  rw [finEquiv_eq_natCast]
  let q := (blockAddress (Nat.pos_of_ne_zero (NeZero.ne d)) s).1
  have h := congrArg (fun z : ℤ => (z : ZMod d))
    (assemble_address (Nat.pos_of_ne_zero (NeZero.ne d)) s)
  change (((q*(d : ℤ)+((timeIndex (d := d) s).val : ℤ)) : ℤ) : ZMod d) =
    (s : ZMod d) at h
  simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,
    mul_zero,zero_add] using h

theorem offset_comp (u : TimedEquiv A B) (v : TimedEquiv B C)
    {d : ℕ} [NeZero d] (b : PathBasis A d) :
    (u.comp v).offset b = u.offset b + v.offset (u.basisEquiv d b) := by
  let c := u.basisEquiv d b
  have he : (u.comp v).equiv b.val.val = translate (countedGraph C)
      (u.phaseInteger b+v.phaseInteger c) ((u.comp v).basisEquiv d b).val.val := by
    calc
      _ = v.equiv (translate (countedGraph B) (u.phaseInteger b) c.val.val) :=
        congrArg v.equiv (u.phase_equation b)
      _ = translate (countedGraph C) (u.phaseInteger b) (v.equiv c.val.val) := v.time _ _
      _ = translate (countedGraph C) (u.phaseInteger b)
          (translate (countedGraph C) (v.phaseInteger c) (v.basisEquiv d c).val.val) :=
        congrArg (translate (countedGraph C) (u.phaseInteger b)) (v.phase_equation c)
      _ = _ := by rw [translate_add,basisEquiv_comp]
  let x := (u.comp v).primitiveEquiv d b.val
  let q := timeIndex (d := d) (u.phaseInteger b+v.phaseInteger c)
  have hq : x.val = (shift C)^[q.val] (canonicalPath x).val.val := by
    change x.val = translate (countedGraph C) (u.phaseInteger b+v.phaseInteger c)
      (canonicalPath x).val.val at he
    exact he.trans (periodic_translate_residue _ (primitivePath_period (canonicalPath x).val) _)
  have h : q = canonicalForwardOffset x := by
    apply Fin.ext
    have hp := (canonicalPath x).val.property
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (f := shift C) (x := (canonicalPath x).val.val)
      (m := q.val) (n := (canonicalForwardOffset x).val)
      (by simpa only [hp] using q.isLt)
      (by simpa only [hp] using (canonicalForwardOffset x).isLt)).mp
        (hq.symm.trans (canonicalForwardOffset_equation x))
  calc
    _ = ZMod.finEquiv d (timeIndex (u.phaseInteger b+v.phaseInteger c)) :=
      congrArg (ZMod.finEquiv d) h.symm
    _ = ((u.phaseInteger b+v.phaseInteger c : ℤ) : ZMod d) := finEquiv_timeIndex _
    _ = _ := by simp only [Int.cast_add,phaseInteger,Int.cast_natCast,offset,finEquiv_eq_natCast,c]

def gyration (u : TimedEquiv A B) (d : ℕ) [NeZero d] : ZMod d :=
  ∑ b : PathBasis A d, u.offset b

/-- The original forward-offset sum depends only on the map on actual
primitive d histories. The finite canonical source basis is the same in both sums. -/
theorem gyration_congr (u v : TimedEquiv A B) (d : ℕ) [NeZero d]
    (h : ∀ x : PrimitivePath A d, u.equiv x.val = v.equiv x.val) :
    u.gyration d = v.gyration d := by
  classical
  unfold gyration
  apply Finset.sum_congr rfl
  intro b _
  exact offset_congr u v h b

theorem gyration_comp (u : TimedEquiv A B) (v : TimedEquiv B C) (d : ℕ) [NeZero d] :
    (u.comp v).gyration d = u.gyration d + v.gyration d := by
  classical
  simp only [gyration,offset_comp,Finset.sum_add_distrib]
  rw [(u.basisEquiv d).sum_comp (fun c => v.offset c)]

theorem gyration_refl (A : CountMat n n) (d : ℕ) [NeZero d] :
    (refl A).gyration d = 0 := by
  classical
  have hz (b : PathBasis A d) : (refl A).offset b = 0 := by
    have he : b.val.val = translate (countedGraph A) 0 (canonicalPath b.val).val.val := by
      rw [canonicalPath_of_basis,translate_zero]
    let q := timeIndex (d := d) (0 : ℤ)
    have hq : b.val.val = (shift A)^[q.val] (canonicalPath b.val).val.val := by
      exact he.trans (periodic_translate_residue _ (primitivePath_period (canonicalPath b.val).val) _)
    have h : q = canonicalForwardOffset b.val := by
      apply Fin.ext
      have hp := (canonicalPath b.val).val.property
      exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (f := shift A) (x := (canonicalPath b.val).val.val)
        (m := q.val) (n := (canonicalForwardOffset b.val).val)
        (by simpa only [hp] using q.isLt)
        (by simpa only [hp] using (canonicalForwardOffset b.val).isLt)).mp
          (hq.symm.trans (canonicalForwardOffset_equation b.val))
    change timeIndex (d := d) (0 : ℤ) = canonicalForwardOffset b.val at h
    have ht : timeIndex (d := d) (0 : ℤ) = 0 := by
      simpa only [Fin.val_zero,Int.natCast_zero] using timeIndex_nat (0 : Fin d)
    change ZMod.finEquiv d (canonicalForwardOffset b.val) = 0
    simpa only [ht,map_zero] using (congrArg (ZMod.finEquiv d) h).symm
  simp only [gyration,hz,Finset.sum_const_zero]

theorem gyration_symm (u : TimedEquiv A B) (d : ℕ) [NeZero d] :
    u.symm.gyration d = -u.gyration d := by
  have hi : u.comp u.symm = refl A := by
    apply ext
    exact u.equiv.symm_apply_apply
  have h := gyration_comp u u.symm d
  rw [hi,gyration_refl] at h
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using h.symm

/-- Basis changes telescope, including both endpoint terms. For a loop the
same actual chart is used at both ends, so its two terms cancel. -/
theorem gyration_basis_change {r s : ℕ} {D : CountMat r r} {E : CountMat s s}
    (left : TimedEquiv D A) (u : TimedEquiv A B) (right : TimedEquiv B E)
    (d : ℕ) [NeZero d] :
    ((left.comp u).comp right).gyration d =
      left.gyration d + u.gyration d + right.gyration d := by
  rw [gyration_comp,gyration_comp]

theorem gyration_conjugate (u : TimedEquiv A A) (c : TimedEquiv A B)
    (d : ℕ) [NeZero d] :
    ((c.symm.comp u).comp c).gyration d = u.gyration d := by
  rw [gyration_basis_change,gyration_symm]
  abel

/-- Finite automorphisms may rotate an orbit: no relabeling-zero rule occurs. -/
def elementary (R : CountMat n m) (S : CountMat m n) : TimedEquiv (R*S) (S*R) :=
  ⟨(elementaryHomeomorph R S).toEquiv,SplitTowerTranslation.positive_time R S⟩

theorem gyration_elementary (R : CountMat n m) (S : CountMat m n)
    (d : ℕ) [NeZero d] :
    (elementary R S).gyration d = relativeForwardGyration (d := d) R S := by
  exact ((orbitBasisEquiv (R*S)).sum_comp (fun b : PathBasis (R*S) d =>
    ZMod.finEquiv d (canonicalForwardOffset (elementaryPrimitiveEquiv R S b.val)))).symm

def timeEquiv (A : CountMat n n) (s : ℤ) : TimedEquiv A A where
  equiv := {
    toFun := translate (countedGraph A) s
    invFun := translate (countedGraph A) (-s)
    left_inv x := by rw [translate_add,neg_add_cancel,translate_zero]
    right_inv x := by rw [translate_add,add_neg_cancel,translate_zero] }
  time t x := by
    change translate (countedGraph A) s (translate (countedGraph A) t x) =
      translate (countedGraph A) t (translate (countedGraph A) s x)
    rw [translate_add,translate_add,add_comm s t]

theorem basisEquiv_time (A : CountMat n n) (s : ℤ) {d : ℕ} [NeZero d]
    (b : PathBasis A d) : (timeEquiv A s).basisEquiv d b = b := by
  apply pathBasis_unique
  apply samePathOrbit_trans (samePathOrbit_symm (canonicalPath_sameOrbit _))
  apply samePathOrbit_symm
  refine ⟨(timeIndex (d := d) s).val,?_⟩
  exact (periodic_translate_residue b.val.val (primitivePath_period b.val) s).symm

theorem offset_time (A : CountMat n n) (s : ℤ) {d : ℕ} [NeZero d]
    (b : PathBasis A d) : (timeEquiv A s).offset b = (s : ZMod d) := by
  have he : (timeEquiv A s).equiv b.val.val = translate (countedGraph A) s
      (canonicalPath ((timeEquiv A s).primitiveEquiv d b.val)).val.val := by
    rw [← basisEquiv_apply,basisEquiv_time]
    rfl
  let x := (timeEquiv A s).primitiveEquiv d b.val
  let q := timeIndex (d := d) s
  have hq : x.val = (shift A)^[q.val] (canonicalPath x).val.val := by
    exact he.trans (periodic_translate_residue _ (primitivePath_period (canonicalPath x).val) _)
  have h : q = canonicalForwardOffset x := by
    apply Fin.ext
    have hp := (canonicalPath x).val.property
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (f := shift A) (x := (canonicalPath x).val.val)
      (m := q.val) (n := (canonicalForwardOffset x).val)
      (by simpa only [hp] using q.isLt)
      (by simpa only [hp] using (canonicalForwardOffset x).isLt)).mp
        (hq.symm.trans (canonicalForwardOffset_equation x))
  change timeIndex (d := d) s = canonicalForwardOffset x at h
  change ZMod.finEquiv d (canonicalForwardOffset _) = _
  rw [← h,finEquiv_timeIndex]

theorem gyration_time (A : CountMat n n) (s : ℤ) (d : ℕ) [NeZero d] :
    (timeEquiv A s).gyration d = (Fintype.card (ActualPathOrbit A d) : ZMod d)*(s : ZMod d) := by
  classical
  rw [gyration]
  simp only [offset_time,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Fintype.card_congr (orbitBasisEquiv A)]
end TimedEquiv
end D5.S3.ConceptDynamics.Coding.CountedRelativeGyrationTransport
