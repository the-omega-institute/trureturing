/- GID: D5/S3/Quantum/Recovery/PhaseBoundaryFlagInstrument
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundaryFlagInstrument
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Common flag instruments and local CPTP decoders preserve finite references. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

variable {S J A B : Type*}
  [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Insert one actual classical flag, with no dependence on an unknown input label. -/
def insertBlock (s : S) :
    CStarMatrix A A ℂ →⋆ₙₐ[ℂ] CStarMatrix (S × A) (S × A) ℂ where
  toFun X := CStarMatrix.ofMatrix fun p q =>
    if p.1 = s ∧ q.1 = s then X p.2 q.2 else 0
  map_zero' := by
    ext p q
    change (if p.1 = s ∧ q.1 = s then (0 : ℂ) else 0) = 0
    split_ifs <;> rfl
  map_add' X Y := by
    ext p q
    change (if p.1 = s ∧ q.1 = s then X p.2 q.2 + Y p.2 q.2 else 0) =
      (if p.1 = s ∧ q.1 = s then X p.2 q.2 else 0) +
        (if p.1 = s ∧ q.1 = s then Y p.2 q.2 else 0)
    split_ifs <;> simp
  map_smul' z X := by
    ext p q
    change (if p.1 = s ∧ q.1 = s then z • X p.2 q.2 else 0) =
      z • (if p.1 = s ∧ q.1 = s then X p.2 q.2 else 0)
    split_ifs <;> simp
  map_star' X := by
    ext ⟨p,i⟩ ⟨q,j⟩
    change (if p = s ∧ q = s then star (X j i) else 0) =
      star (if q = s ∧ p = s then X j i else 0)
    by_cases h : p = s ∧ q = s <;> simp [h,and_comm]
  map_mul' X Y := by
    ext ⟨p,i⟩ ⟨q,j⟩
    change (if p = s ∧ q = s then (X * Y) i j else 0) =
      ∑ t : S × A,
        (if p = s ∧ t.1 = s then X i t.2 else 0) *
          (if t.1 = s ∧ q = s then Y t.2 j else 0)
    by_cases hp : p = s <;> by_cases hq : q = s <;>
      simp [hp, hq, Fintype.sum_prod_type, CStarMatrix.mul_apply]

/-- Output-label compression is completely positive at every amplification. -/
def compressBlock (s : S) :
    CompletelyPositiveMap (CStarMatrix (S × A) (S × A) ℂ) (CStarMatrix A A ℂ) where
  toLinearMap :=
    { toFun := fun X => CStarMatrix.ofMatrix fun i j => X (s,i) (s,j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_cstarMatrix_nonneg' k X hX := by
    have hflat : 0 ≤ flattenCStar k X := map_nonneg (flattenCStar k) hX
    have hmatrix : (CStarMatrix.ofMatrix.symm (flattenCStar k X)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hflat)
    have hsmall := hmatrix.submatrix (fun p : A × Fin k => ((s,p.1),p.2))
    have hout : 0 ≤ flattenCStar k
        (X.map (fun Y => CStarMatrix.ofMatrix fun i j => Y (s,i) (s,j))) :=
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hsmall.nonneg
    exact map_nonneg (flattenCStar k).symm hout

private def composeCP {C : Type*} [Fintype C] [DecidableEq C]
    (g : CompletelyPositiveMap (CStarMatrix B B ℂ) (CStarMatrix C C ℂ))
    (f : CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix B B ℂ)) :
    CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix C C ℂ) where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_cstarMatrix_nonneg' k X hX := by
    change 0 ≤ (X.map f).map g
    exact g.map_cstarMatrix_nonneg (X.map f) (f.map_cstarMatrix_nonneg X hX)

private theorem cstar_sum_apply {T U V R : Type*} [Fintype T] [AddCommMonoid R]
    (X : T → CStarMatrix U V R) (i : U) (j : V) :
    (∑ t, X t) i j = ∑ t, X t i j := by
  let ev : CStarMatrix U V R →+ R :=
    { toFun := fun M => M i j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev X Finset.univ

private def sumCP
    (f : J → S → CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix B B ℂ)) :
    CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix B B ℂ) where
  toLinearMap := ∑ j, ∑ s, (f j s).toLinearMap
  map_cstarMatrix_nonneg' k X hX := by
    have heq : X.map (⇑(∑ j, ∑ s, (f j s).toLinearMap)) =
        ∑ j, ∑ s, X.map (f j s) := by
      ext p q
      simp only [CStarMatrix.map_apply, LinearMap.sum_apply, cstar_sum_apply]
      rfl
    rw [heq]
    exact Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun s _ => (f j s).map_cstarMatrix_nonneg X hX

omit [DecidableEq S] [DecidableEq J] [DecidableEq A] [DecidableEq B] in
private theorem sumCP_apply
    (f : J → S → CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix B B ℂ))
    (X : CStarMatrix A A ℂ) : sumCP f X = ∑ j, ∑ s, f j s X := by
  change (∑ j, ∑ s, (f j s).toLinearMap) X = _
  simp only [LinearMap.sum_apply]
  rfl

/-- Every branch is CP; their sum preserves trace for each actual flag.
There is no chosen Kraus representation and no restriction on its rank. -/
structure FlagInstrument where
  operation : J → S → CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix B B ℂ)
  trace_preserving : ∀ s (X : CStarMatrix A A ℂ),
    (∑ j, Matrix.trace (operation j s X)) = Matrix.trace X

omit [DecidableEq A] in
private theorem trace_insert (s : S) (X : CStarMatrix A A ℂ) :
    Matrix.trace (insertBlock s X) = Matrix.trace X := by
  change (∑ p : S × A, if p.1 = s ∧ p.1 = s then X p.2 p.2 else 0) = _
  simp [Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply]

private theorem sum_trace_compress (X : CStarMatrix (S × A) (S × A) ℂ) :
    (∑ s, Matrix.trace (compressBlock s X)) = Matrix.trace X := by
  change (∑ s, ∑ i : A, X (s,i) (s,i)) = ∑ p : S × A, X p p
  exact (Fintype.sum_prod_type (fun p : S × A => X p p)).symm

private theorem compress_insert (t s : S) (X : CStarMatrix A A ℂ) :
    compressBlock t (insertBlock s X) = if t = s then X else 0 := by
  ext i j
  change (if t = s ∧ t = s then X i j else 0) = (if t = s then X else 0) i j
  by_cases h : t = s <;> simp [h]

omit [Fintype S] [DecidableEq S] [DecidableEq J] [DecidableEq A] [DecidableEq B] in
private theorem instrument_ext
    {Γ Δ : FlagInstrument (S := S) (J := J) (A := A) (B := B)}
    (h : Γ.operation = Δ.operation) : Γ = Δ := by
  cases Γ
  cases Δ
  cases h
  rfl

namespace FlagInstrument

/-- Read the actual flag, apply the same branch family, record its output label,
and discard the input flag. Both registers belong to the receiver. -/
def decoder (Γ : FlagInstrument (S := S) (J := J) (A := A) (B := B)) :
    QuantumChannel (S × A) (J × B) where
  toCompletelyPositiveMap := sumCP fun j s =>
    composeCP (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (insertBlock j))
      (composeCP (Γ.operation j s) (compressBlock s))
  trace_preserving X := by
    rw [sumCP_apply]
    change Matrix.trace (∑ j, ∑ s, insertBlock j
      (Γ.operation j s (compressBlock s X))) = Matrix.trace X
    simp_rw [Matrix.trace_sum, trace_insert]
    rw [Finset.sum_comm]
    simp_rw [Γ.trace_preserving]
    exact sum_trace_compress X

/-- Extract the branch operations of an arbitrary all-CPTP receiver decoder. -/
def extract (D : QuantumChannel (S × A) (J × B)) :
    FlagInstrument (S := S) (J := J) (A := A) (B := B) where
  operation j s := composeCP (compressBlock j)
    (composeCP D.toCompletelyPositiveMap
      (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (insertBlock s)))
  trace_preserving s X := by
    change (∑ j, Matrix.trace (compressBlock j
      (D.toCompletelyPositiveMap (insertBlock s X)))) = Matrix.trace X
    rw [sum_trace_compress, D.trace_preserving, trace_insert]

end FlagInstrument

/-- The branch action on an arbitrary untouched reference, which can include
both the inaccessible source memory and an external reference. -/
def instrumentReference {F : Type*} [Fintype F] [DecidableEq F]
    (Γ : FlagInstrument (S := S) (J := J) (A := A) (B := B))
    (X : CStarMatrix (F × (S × A)) (F × (S × A)) ℂ) :
    CStarMatrix (F × (J × B)) (F × (J × B)) ℂ :=
  CStarMatrix.ofMatrix fun p q => if p.2.1 = q.2.1 then
    ∑ s, Γ.operation p.2.1 s
      (CStarMatrix.ofMatrix fun a c => X (p.1,(s,a)) (q.1,(s,c))) p.2.2 q.2.2
    else 0

/-- A flag-diagonal state can retain arbitrary coherences in every other system. -/
def FlagDiagonal {F : Type*} [Fintype F] [DecidableEq F]
    (X : CStarMatrix (F × (S × A)) (F × (S × A)) ℂ) : Prop :=
  ∀ p q, p.2.1 ≠ q.2.1 → X p q = 0

/-- Pinch only the receiver's output label; neither reference is acted on. -/
def outputLabelPinch {F : Type*} [Fintype F] [DecidableEq F]
    (Y : CStarMatrix (F × (J × B)) (F × (J × B)) ℂ) :
    CStarMatrix (F × (J × B)) (F × (J × B)) ℂ :=
  CStarMatrix.ofMatrix fun p q => if p.2.1 = q.2.1 then Y p q else 0

private theorem decoder_reference {F : Type*} [Fintype F] [DecidableEq F]
    (Γ : FlagInstrument (S := S) (J := J) (A := A) (B := B))
    (X : CStarMatrix (F × (S × A)) (F × (S × A)) ℂ) :
    referenceAction Γ.decoder X = instrumentReference Γ X := by
  ext ⟨r,j,b⟩ ⟨t,k,c⟩
  change Γ.decoder.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix fun p q => X (r,p) (t,q)) (j,b) (k,c) = _
  dsimp only [FlagInstrument.decoder]
  rw [sumCP_apply]
  simp only [cstar_sum_apply]
  change (∑ l : J, ∑ s : S, if j = l ∧ k = l then
    Γ.operation l s (CStarMatrix.ofMatrix fun a d => X (r,(s,a)) (t,(s,d))) b c else 0) =
    if j = k then ∑ s, Γ.operation j s
      (CStarMatrix.ofMatrix fun a d => X (r,(s,a)) (t,(s,d))) b c else 0
  by_cases hjk : j = k
  · subst k
    simp
  · have hzero (l : J) : ¬ (j = l ∧ k = l) := by
      rintro ⟨rfl,rfl⟩
      exact hjk rfl
    simp [hjk,hzero]

private theorem extract_decoder
    (Γ : FlagInstrument (S := S) (J := J) (A := A) (B := B)) :
    FlagInstrument.extract Γ.decoder = Γ := by
  apply instrument_ext
  funext j s
  apply DFunLike.ext
  intro X
  change compressBlock j (Γ.decoder.toCompletelyPositiveMap (insertBlock s X)) = _
  dsimp only [FlagInstrument.decoder]
  rw [sumCP_apply]
  change compressBlock j (∑ l, ∑ t, insertBlock l
    (Γ.operation l t (compressBlock t (insertBlock s X)))) = Γ.operation j s X
  simp_rw [map_sum, compress_insert]
  ext b c
  simp only [cstar_sum_apply]
  simp_rw [apply_ite, map_zero]
  have eval_ite (p : Prop) [Decidable p] (Y : CStarMatrix B B ℂ) :
      (if p then Y else 0) b c = if p then Y b c else 0 := by
    split_ifs <;> rfl
  simp only [eval_ite]
  simp [eq_comm]

private theorem extract_reference {F : Type*} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (S × A) (J × B))
    (X : CStarMatrix (F × (S × A)) (F × (S × A)) ℂ) (hX : FlagDiagonal X) :
    instrumentReference (FlagInstrument.extract D) X =
      outputLabelPinch (referenceAction D X) := by
  have decomposition (r t : F) :
      (CStarMatrix.ofMatrix fun p q : S × A => X (r,p) (t,q)) =
        ∑ s, insertBlock s (CStarMatrix.ofMatrix fun a c => X (r,(s,a)) (t,(s,c))) := by
    ext ⟨s,a⟩ ⟨v,c⟩
    simp only [CStarMatrix.ofMatrix_apply, cstar_sum_apply]
    change X (r,(s,a)) (t,(v,c)) =
      ∑ u, if s = u ∧ v = u then X (r,(u,a)) (t,(u,c)) else 0
    by_cases hsv : s = v
    · subst v
      simp
    · have hz := hX (r,(s,a)) (t,(v,c)) hsv
      have hzero (u : S) : ¬ (s = u ∧ v = u) := by
        rintro ⟨rfl,rfl⟩
        exact hsv rfl
      simp [hz,hzero]
  ext ⟨r,j,b⟩ ⟨t,k,c⟩
  change (if j = k then ∑ s, (FlagInstrument.extract D).operation j s
    (CStarMatrix.ofMatrix fun a d => X (r,(s,a)) (t,(s,d))) b c else 0) =
    if j = k then referenceAction D X (r,(j,b)) (t,(k,c)) else 0
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl, if_pos rfl]
    change (∑ s, D.toCompletelyPositiveMap
      (insertBlock s (CStarMatrix.ofMatrix fun a d => X (r,(s,a)) (t,(s,d)))) (j,b) (j,c)) =
      D.toCompletelyPositiveMap (CStarMatrix.ofMatrix fun p q => X (r,p) (t,q)) (j,b) (j,c)
    rw [decomposition, map_sum]
    simp only [cstar_sum_apply]
  · simp only [if_neg hjk]

/-- A common flag instrument has one CPTP realization on the full receiver
space, with exact action on every finite reference. Conversely every CPTP
decoder induces a lawful instrument whose realization is its output-label
pinching on flag-diagonal inputs. No Kraus rank or source-memory access is added. -/
theorem common_flag_instrument_complete :
    (∀ Γ : FlagInstrument (S := S) (J := J) (A := A) (B := B),
      ∃ D : QuantumChannel (S × A) (J × B),
        FlagInstrument.extract D = Γ ∧
        ∀ (F : Type*) [Fintype F] [DecidableEq F]
          (X : CStarMatrix (F × (S × A)) (F × (S × A)) ℂ),
          referenceAction D X = instrumentReference Γ X) ∧
    (∀ (D : QuantumChannel (S × A) (J × B))
      (F : Type*) [Fintype F] [DecidableEq F]
      (X : CStarMatrix (F × (S × A)) (F × (S × A)) ℂ),
      FlagDiagonal X →
        referenceAction (FlagInstrument.extract D).decoder X =
          outputLabelPinch (referenceAction D X)) := by
  constructor
  · intro Γ
    exact ⟨Γ.decoder, extract_decoder Γ, fun _ _ _ X => decoder_reference Γ X⟩
  · intro D F _ _ X hX
    rw [decoder_reference]
    exact extract_reference D X hX

end D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
