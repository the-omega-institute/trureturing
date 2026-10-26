/- GID: D5/S3/Observer/CubicGain/OriginalWorld
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/OriginalWorld
   mirror-E: none(waiver:original-world-topology-and-coefficient-control)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.OfFn]
   utility: none
   digest: Original polynomial coefficient worlds and the unrestricted parent have the same topology. -/

import D5.S3.Observer.CubicGain.ResponseProper
import Mathlib.Algebra.Polynomial.OfFn

/-! Original matrices, ordinary polynomial coefficients and the literal parent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain

/-- Coefficients of the same whole polynomial, in ascending order. -/
def gainCoefficients (a : Gain) : Gain :=
  ![a 0, -11/6*a 0+3*a 1-3/2*a 2+1/3*a 3,
    a 0-5/2*a 1+2*a 2-1/2*a 3, -1/6*a 0+1/2*a 1-1/2*a 2+1/6*a 3]

private theorem coefficients_polynomial (a : Gain) :
    Polynomial.ofFn 4 (gainCoefficients a)=gainPoly a := by
  apply Polynomial.funext
  intro s
  simp [Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four,gainCoefficients,gainPoly]
  ring

private theorem coefficient_degree (c : Gain) : (Polynomial.ofFn 4 c).degree ≤ 3 :=
  Polynomial.degree_le_of_natDegree_le
    (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) c))

/-- The last coordinate stores all four ordinary polynomial coefficients. -/
abbrev OriginalWorld := ℝ × ℝ × ℝ × Gain

def originalPolynomial (W : OriginalWorld) : Polynomial ℝ := Polynomial.ofFn 4 W.2.2.2

def originalRead (W : OriginalWorld) (i : ℕ) : ℝ :=
  W.2.2.1+(originalPolynomial W).eval (i : ℝ)*
    Matrix.trace (chronological i*sourceMatrix W.1 W.2.1)

def OriginalParent (W : OriginalWorld) : Prop :=
  0 < W.1 ∧ W.1 < 1 ∧ 0 < W.2.1 ∧ originalPolynomial W ≠ 0 ∧
    ∀ i : Fin 5, originalRead W i=history i

def originalResponse (W : OriginalWorld) : ℝ × ℝ :=
  (originalRead W 5,originalRead W 6)

def encodeWorld (W : World) : OriginalWorld :=
  (W.1,W.2.1,W.2.2.1,gainCoefficients W.2.2.2)

def decodeWorld (W : OriginalWorld) : World :=
  (W.1,W.2.1,W.2.2.1,fun i => (originalPolynomial W).eval (i : ℕ))

private theorem decoded_polynomial (W : OriginalWorld) :
    gainPoly (decodeWorld W).2.2.2=originalPolynomial W :=
  (polynomial_representation _ (coefficient_degree W.2.2.2)).symm

private theorem decoded_read (W : OriginalWorld) (i : ℕ) :
    literalRead (decodeWorld W) i=originalRead W i := by
  dsimp [literalRead,originalRead,decodeWorld,traceAt]
  rw [← gainPoly_eval]
  have hh : gainPoly (fun i : Fin 4 => (originalPolynomial W).eval (i : ℕ))=originalPolynomial W :=
    decoded_polynomial W
  rw [hh]

private theorem encoded_read (W : World) (i : ℕ) :
    originalRead (encodeWorld W) i=literalRead W i := by
  dsimp [originalRead,originalPolynomial,encodeWorld,literalRead,traceAt]
  rw [coefficients_polynomial,gainPoly_eval]

private theorem decode_encode (W : World) : decodeWorld (encodeWorld W)=W := by
  obtain ⟨r,b,d,a⟩ := W
  dsimp [decodeWorld,encodeWorld,originalPolynomial]
  rw [coefficients_polynomial]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  ext i
  change (gainPoly a).eval (i : ℝ)=a i
  rw [gainPoly_eval,gain_samples]

private theorem encode_decode (W : OriginalWorld) : encodeWorld (decodeWorld W)=W := by
  obtain ⟨r,b,d,c⟩ := W
  dsimp [encodeWorld,decodeWorld]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  apply Polynomial.injective_ofFn 4
  rw [coefficients_polynomial]
  exact (polynomial_representation _ (coefficient_degree c)).symm

private theorem decoded_parent (W : OriginalWorld) :
    LiteralParent (decodeWorld W) ↔ OriginalParent W := by
  constructor
  · intro h
    refine ⟨h.1,h.2.1,h.2.2.1,?_,?_⟩
    · rw [← decoded_polynomial]
      exact parent_gain_nonzero _ h
    · intro i
      rw [← decoded_read]
      exact h.2.2.2 i
  · rintro ⟨hr,hr1,hb,_,hrows⟩
    refine ⟨hr,hr1,hb,?_⟩
    intro i
    rw [decoded_read]
    exact hrows i

abbrev OriginalOverOpen :=
  {W : OriginalWorld // OriginalParent W ∧ originalResponse W ∈ responseOpen}

def originalResponseOverOpen (W : OriginalOverOpen) : responseOpen :=
  ⟨originalResponse W.1,W.2.2⟩

private theorem parent_literal (C : Coordinates) (hC : StrictParent C) :
    LiteralParent (parentWorld C) := by
  apply (parent_world_iff _).mpr
  have hcoord : worldCoordinates (parentWorld C)=C := by
    obtain ⟨r,b,e⟩ := C
    simp [worldCoordinates,parentWorld]
  rw [hcoord]
  exact ⟨hC,rfl⟩

private theorem encoded_parent (C : Coordinates) (hC : StrictParent C) :
    OriginalParent (encodeWorld (parentWorld C)) := by
  apply (decoded_parent _).mp
  rw [decode_encode]
  exact parent_literal C hC

private theorem encoded_response (C : Coordinates) :
    originalResponse (encodeWorld (parentWorld C))=response C := by
  obtain ⟨h5,h6⟩ := actual_m_responses C
  apply Prod.ext <;> dsimp [originalResponse,response]
  · rw [encoded_read,h5]
  · rw [encoded_read,h6]

theorem original_coordinates (W : OriginalWorld) (hW : OriginalParent W) :
    StrictParent (worldCoordinates (decodeWorld W)) ∧
    encodeWorld (parentWorld (worldCoordinates (decodeWorld W)))=W ∧
    response (worldCoordinates (decodeWorld W))=originalResponse W := by
  have hw := (decoded_parent W).mpr hW
  obtain ⟨hc,he⟩ := (parent_world_iff _).mp hw
  refine ⟨hc,?_,?_⟩
  · rw [he,encode_decode]
  · rw [← encoded_response,he,encode_decode]

/-- This is a homeomorphism for ordinary coefficient topology; neither source
nor gain is normalized, and all strict parent worlds occur. -/
def originalParentHomeomorph : ParentOverOpen ≃ₜ OriginalOverOpen where
  toFun C := ⟨encodeWorld (parentWorld C.1),encoded_parent _ C.2.1,
    by rw [encoded_response]; exact C.2.2⟩
  invFun W := ⟨worldCoordinates (decodeWorld W.1),
    (original_coordinates _ W.2.1).1,
    by rw [(original_coordinates _ W.2.1).2.2]; exact (originalResponseOverOpen W).2⟩
  left_inv := by
    intro C
    apply Subtype.ext
    change worldCoordinates (decodeWorld (encodeWorld (parentWorld C.1)))=C.1
    rw [decode_encode]
    simp [worldCoordinates,parentWorld]
  right_inv := by
    intro W
    apply Subtype.ext
    exact (original_coordinates _ W.2.1).2.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro C
    obtain ⟨hj,hn,ht,hu⟩ := source_positivity C.1.1 C.1.2.1
      C.2.1.1.le C.2.1.2.1.le C.2.1.2.2.1
    have hb := C.2.1.2.2.1
    dsimp [encodeWorld,parentWorld,gainCoefficients,parentGain,sourceJ,sourceN]
    fun_prop (disch := first | exact ne_of_gt hj | exact ne_of_gt hn | exact ne_of_gt ht | exact ne_of_gt hu | exact ne_of_gt hb)
  continuous_invFun := by
    apply Continuous.subtype_mk
    dsimp [worldCoordinates,decodeWorld]
    fun_prop

/-- The uniform estimate controls the fixed drift and all ordinary polynomial
coefficients, without assuming any sample is nonzero. -/
theorem bounded_response_coefficients (M : ℝ) :
    ∃ D G : ℝ, ∀ W : OriginalWorld, OriginalParent W → |(originalResponse W).1| ≤ M →
      |W.2.2.1| ≤ D ∧ ∀ i : Fin 4, |W.2.2.2 i| ≤ G := by
  obtain ⟨D,G,hbound⟩ := bounded_fifth_bounds_whole_gain M
  let D' := max D 0
  let G' := max G 0
  refine ⟨24+D',10*G',?_⟩
  intro W hW hp
  obtain ⟨hC,hencode,hresp⟩ := original_coordinates W hW
  have hfifth : |fifthResponse (worldCoordinates (decodeWorld W))| ≤ M := by
    change |(response (worldCoordinates (decodeWorld W))).1| ≤ M
    rw [hresp]
    exact hp
  obtain ⟨hd,hg⟩ := hbound _ hC hfifth
  have hd' : |W.2.2.1-24| ≤ D' := hd.trans (le_max_left _ _)
  have hg' (i : Fin 4) : |parentGain (worldCoordinates (decodeWorld W)) i| ≤ G' :=
    (hg i).trans (le_max_left _ _)
  have hG : 0 ≤ G' := le_max_right _ _
  constructor
  · have hh := abs_le.mp hd'
    apply abs_le.mpr
    constructor <;> linarith
  · have hc : gainCoefficients (parentGain (worldCoordinates (decodeWorld W)))=W.2.2.2 :=
      congrArg (fun w : OriginalWorld => w.2.2.2) hencode
    rw [← hc]
    intro i
    have h0 := abs_le.mp (hg' 0)
    have h1 := abs_le.mp (hg' 1)
    have h2 := abs_le.mp (hg' 2)
    have h3 := abs_le.mp (hg' 3)
    fin_cases i <;> norm_num [gainCoefficients] <;> apply abs_le.mpr <;>
      constructor <;> linarith

#print axioms originalParentHomeomorph
#print axioms bounded_response_coefficients

end D5.S3.Observer.CubicGain
