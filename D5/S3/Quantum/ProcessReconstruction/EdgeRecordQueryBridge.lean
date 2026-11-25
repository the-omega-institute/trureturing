/- GID: D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Translated path-record channels realize the hidden-input query family. -/

import D5.S3.Quantum.ProcessReconstruction.EdgeRecordDilation
import D5.S3.Quantum.ProcessReconstruction.EdgeRecordDistance
import D5.S3.Quantum.ProcessReconstruction.EdgeRecordQueryBound

/-! Local input translations carry the record realization and paired Choi properties
to the entire hidden-input family. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.EnvironmentRecords.EdgePath

open Matrix UnitaryReconstruction
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open UnitaryReconstruction.LiuWildChoiObstruction (normalizedChoi normalizedChoi_entry pairMatrix)
open HiddenInput (AdaptiveProtocol BinaryPOVM bornMass markedChannel markedMass
  markedChannel_action markedPrepared preparationChannel)

variable {n : ℕ}

/-- Translate the input by the word whose support is the set of sites where the mark is zero. -/
def activate (a : Word (n + 1)) : Equiv.Perm (Word (n + 1)) where
  toFun x := x + (allOn - a)
  invFun x := x - (allOn - a)
  left_inv x := add_sub_cancel_right x _
  right_inv x := sub_add_cancel x _

theorem activate_site (a x : Word (n + 1)) (i : Fin (n + 1)) :
    activate a x i = x i + (1 - a i) := rfl

theorem activate_eq_allOn (a x : Word (n + 1)) : activate a x = allOn ↔ x = a := by
  have ha : activate a a = allOn := by
    change a + (allOn - a) = allOn
    abel
  rw [← ha]
  exact (activate a).injective.eq_iff

/-- The exact row mass is the pushforward of the original independent edge and site records. -/
theorem markedMass_eq_push (a : Word (n + 1)) (b : Bit) (x y : Word (n + 1)) :
    markedMass a b x y = push (localOutput b (activate a x)) y := by
  change markedMass a b x y = kernel b (activate a x) y
  by_cases hx : x = a
  · rw [(activate_eq_allOn a x).2 hx, kernel_allOn]
    have hp : HiddenInput.parity y = parity y := rfl
    simp only [HiddenInput.markedMass, hx, ite_true, HiddenInput.parityMass, hp,
      HiddenInput.uniformMass, div_eq_mul_inv]
  · rw [kernel_inactive b (mt (activate_eq_allOn a x).1 hx)]
    simp [HiddenInput.markedMass, hx, HiddenInput.uniformMass]

/-- The path channel with the original prepared states selected by the translated input. -/
def activatedChannel (a : Word (n + 1)) (b : Bit) :
    QuantumChannel (Word (n + 1)) (Word (n + 1)) :=
  preparationChannel fun x => prepared b (activate a x)

theorem markedChannel_eq_activatedChannel (a : Word (n + 1)) (b : Bit) :
    markedChannel a b = activatedChannel a b := by
  have h : markedPrepared a b = fun x => prepared b (activate a x) := by
    funext x
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change diagonal (fun y => (markedMass a b x y : ℂ)) =
      diagonal (fun y => (kernel b (activate a x) y : ℂ))
    simp only [markedMass_eq_push, kernel]
  exact congrArg preparationChannel h

theorem markedChannel_action_eq_translated (a : Word (n + 1)) (b : Bit)
    (X : Matrix (Word (n + 1)) (Word (n + 1)) ℂ) :
    Action (markedChannel a b) X =
      Action (channel b) (X.submatrix (activate a).symm (activate a).symm) := by
  change Foundation.FiniteTraceDistance.act (markedChannel a b) X =
    Action (channel b) (X.submatrix (activate a).symm (activate a).symm)
  rw [markedChannel_action, channel_action]
  apply congrArg diagonal
  funext y
  simpa only [markedMass_eq_push, kernel, Function.comp_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using
    (Equiv.sum_comp (activate a) (fun z =>
      X ((activate a).symm z) ((activate a).symm z) * (kernel b z y : ℂ)))

/-- Precompose the verified record dilation by the computational basis permutation. -/
def activatedDilation (a : Word (n + 1)) (b : Bit) :
    Matrix (Word (n + 1) × Environment n) (Word (n + 1)) ℂ :=
  (dilation b).submatrix id (activate a)

theorem activatedDilation_isometry (a : Word (n + 1)) (b : Bit) :
    (activatedDilation a b)ᴴ * activatedDilation a b = 1 := by
  change (dilation b)ᴴ.submatrix (activate a) id * (dilation b).submatrix id (activate a) = 1
  rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, dilation_isometry]
  exact Matrix.submatrix_one_equiv (activate a)

theorem trace_activatedDilation (a : Word (n + 1)) (b : Bit)
    (X : Matrix (Word (n + 1)) (Word (n + 1)) ℂ) :
    partialTraceRight (activatedDilation a b * X * (activatedDilation a b)ᴴ) =
      Action (activatedChannel a b) X := by
  have hX : X = (X.submatrix (activate a).symm (activate a).symm).submatrix
      (activate a) (activate a) := by
    ext i j
    simp
  conv_lhs => rw [hX]
  change partialTraceRight
    ((dilation b).submatrix id (activate a) *
      (X.submatrix (activate a).symm (activate a).symm).submatrix (activate a) (activate a) *
      (dilation b)ᴴ.submatrix (activate a) id) = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    trace_environment_eq_channel, ← markedChannel_eq_activatedChannel,
    markedChannel_action_eq_translated]

/-- The translation on the Choi reference, with the output index fixed. -/
def pairedActivation (a : Word (n + 1)) : Equiv.Perm (Word (n + 1) × Word (n + 1)) :=
  (activate a).prodCongr (Equiv.refl _)

theorem activatedChoi_eq_relabel (a : Word (n + 1)) (b : Bit) :
    normalizedChoi (activatedChannel a b) =
      relabelState (pairedActivation a) (normalizedChoi (channel b)) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨x,y⟩ ⟨z,w⟩
  change pairMatrix (normalizedChoi (activatedChannel a b)) (x,y) (z,w) =
    pairMatrix (normalizedChoi (channel b)) (activate a x,y) (activate a z,w)
  rw [normalizedChoi_entry, normalizedChoi_entry, ← markedChannel_eq_activatedChannel]
  change _ * Action (markedChannel a b) (Matrix.single x z 1) y w =
    _ * Action (channel b) (Matrix.single (activate a x) (activate a z) 1) y w
  rw [markedChannel_action_eq_translated]
  have h : (Matrix.single x z (1 : ℂ)).submatrix (activate a).symm (activate a).symm =
      Matrix.single (activate a x) (activate a z) 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.single_apply, (activate a).eq_symm_apply]
  rw [h]

/-- Coordinatewise translation on any specified set of input sites. -/
private def translateOn {I : Type*} (sites : I → Fin (n + 1)) (a : Word (n + 1)) :
    Equiv.Perm (I → Bit) :=
  Equiv.piCongrRight fun i => Equiv.addRight (1 - a (sites i))

private theorem splitPair_activate (a : Word (n + 1)) (s : Mask n)
    (w : Discarded s × Discarded s) (p : Kept s × Kept s) :
    pairedActivation a ((splitPair s).symm (w,p)) =
      (splitPair s).symm
        ((translateOn Subtype.val a w.1,w.2), (translateOn Subtype.val a p.1,p.2)) := by
  apply (splitPair s).injective
  rw [Equiv.apply_symm_apply]
  have h (q : Word (n + 1) × Word (n + 1)) :
      splitPair s (pairedActivation a q) =
        ((translateOn Subtype.val a (splitPair s q).1.1, (splitPair s q).1.2),
          (translateOn Subtype.val a (splitPair s q).2.1, (splitPair s q).2.2)) := rfl
  rw [h, Equiv.apply_symm_apply]

private theorem pairedMarginal_activate (a : Word (n + 1)) (s : Mask n)
    (ρ : DensityState (Word (n + 1) × Word (n + 1))) :
    pairedMarginal s (relabelState (pairedActivation a) ρ) =
      relabelState ((translateOn Subtype.val a).prodCongr (Equiv.refl (Kept s)))
        (pairedMarginal s ρ) := by
  let e : Equiv.Perm (Discarded s × Discarded s) :=
    (translateOn Subtype.val a).prodCongr (Equiv.refl _)
  let k : Equiv.Perm (Kept s × Kept s) :=
    (translateOn Subtype.val a).prodCongr (Equiv.refl _)
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext p q
  change (∑ w : Discarded s × Discarded s,
    pairMatrix ρ (pairedActivation a ((splitPair s).symm (w,p)))
      (pairedActivation a ((splitPair s).symm (w,q)))) =
    ∑ w : Discarded s × Discarded s,
      pairMatrix ρ ((splitPair s).symm (w,k p)) ((splitPair s).symm (w,k q))
  simp_rw [splitPair_activate]
  exact Equiv.sum_comp e (fun w =>
    pairMatrix ρ ((splitPair s).symm (w,k p)) ((splitPair s).symm (w,k q)))

theorem activated_proper_paired_mixed (a : Word (n + 1)) (b : Bit) (s : Mask n)
    (hs : s ≠ Finset.univ) :
    pairMatrix (pairedMarginal s (normalizedChoi (activatedChannel a b))) =
      diagonal (fun _ : Kept s × Kept s =>
        ((Fintype.card (Kept s × Kept s) : ℝ)⁻¹ : ℂ)) := by
  rw [activatedChoi_eq_relabel, pairedMarginal_activate]
  change (pairMatrix (pairedMarginal s (normalizedChoi (channel b)))).submatrix _ _ = _
  rw [proper_paired_mixed b s hs, Matrix.submatrix_diagonal_equiv]
  rfl

/-- All proper paired windows have the same full density data for every mark and parity. -/
theorem activated_properPairedData_eq (a a' : Word (n + 1)) (b b' : Bit) :
    properPairedData (activatedChannel a b) = properPairedData (activatedChannel a' b') := by
  funext s
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  exact (activated_proper_paired_mixed a b s.val s.property).trans
    (activated_proper_paired_mixed a' b' s.val s.property).symm

theorem activated_pairedEntropy (a : Word (n + 1)) (b : Bit) (s : Mask n) :
    vonNeumannEntropy (pairedMarginal s (normalizedChoi (activatedChannel a b))) =
      vonNeumannEntropy (pairedMarginal s (normalizedChoi (channel b))) := by
  rw [activatedChoi_eq_relabel, pairedMarginal_activate]
  exact entropy_relabelState _ _

theorem activated_pairedCMI (a : Word (n + 1)) (b : Bit) (L M R : Mask n) :
    pairedCMI (normalizedChoi (activatedChannel a b)) L M R =
      pairedCMI (normalizedChoi (channel b)) L M R := by
  simp only [pairedCMI, activated_pairedEntropy]

theorem activated_pairedCMI_formula (a : Word (n + 1)) (b : Bit) (L M R : Mask n)
    (hLM : Disjoint L M) (hLR : Disjoint L R) (hMR : Disjoint M R) :
    pairedCMI (normalizedChoi (activatedChannel a b)) L M R =
      if L = ∅ ∨ R = ∅ then 0
      else if L ∪ M ∪ R = Finset.univ then Real.log 2 / dimension n else 0 := by
  rw [activated_pairedCMI]
  exact choi_pairedCMI b L M R hLM hLR hMR

theorem activated_pairedCMI_decay (a : Word (n + 1)) (b : Bit) (L M R : Mask n)
    (hLM : Disjoint L M) (hLR : Disjoint L R) (hMR : Disjoint M R) :
    pairedCMI (normalizedChoi (activatedChannel a b)) L M R ≤
      Real.log 2 * Real.exp (-Real.log 2 * M.card) := by
  rw [activated_pairedCMI]
  exact choi_pairedCMI_decay b L M R hLM hLR hMR

theorem activated_pair_diamond (a : Word (n + 1)) :
    diamondDistance (activatedChannel a 0) (activatedChannel a 1) = 2 := by
  rw [← markedChannel_eq_activatedChannel, ← markedChannel_eq_activatedChannel]
  exact HiddenInput.markedPair_diamond a

section Query

variable {T : ℕ} {R : Type} [Fintype R] [DecidableEq R]

/-- The decision may receive the mark after the last call. The protocol is fixed across marks. -/
theorem activated_query_lower_bound (P : AdaptiveProtocol n T R)
    (E : Word (n + 1) → BinaryPOVM (R × Word (n + 1)))
    (h0 : ∀ a, 2 / 3 ≤ (E a).probZero (P.terminal (activatedChannel a 0)))
    (h1 : ∀ a, 2 / 3 ≤ (E a).probOne (P.terminal (activatedChannel a 1))) :
    (2 : ℝ) ^ (n + 1) / 3 ≤ T :=
  P.query_lower_bound E
    (by simpa only [markedChannel_eq_activatedChannel] using h0)
    (by simpa only [markedChannel_eq_activatedChannel] using h1)

/-- Reconstruction with finite classical output inherits the bound for the path family. -/
theorem activated_reconstruction_query_lower_bound (P : AdaptiveProtocol n T R)
    {Ω : Type*} [Fintype Ω]
    (effect : Ω → Matrix (R × Word (n + 1)) (R × Word (n + 1)) ℂ)
    (positive : ∀ o, (effect o).PosSemidef) (complete : ∑ o, effect o = 1)
    (estimate : Ω → QuantumChannel (Word (n + 1)) (Word (n + 1)))
    (success : ∀ a b, 2 / 3 ≤
      ∑ o ∈ Finset.univ.filter
        (fun o => diamondDistance (activatedChannel a b) (estimate o) < 1),
        bornMass effect (P.terminal (activatedChannel a b)) o) :
    (2 : ℝ) ^ (n + 1) / 3 ≤ T :=
  P.reconstruction_query_lower_bound effect positive complete estimate
    (by simpa only [markedChannel_eq_activatedChannel] using success)

end Query

end D5.S3.Quantum.EnvironmentRecords.EdgePath
