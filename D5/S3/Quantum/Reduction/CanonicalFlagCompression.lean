/- GID: D5/S3/Quantum/Reduction/CanonicalFlagCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/CanonicalFlagCompression
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Arbitrary canonical CPTP classical-flag encoders and decoders factor through actual normalized finite Kraus ports. -/

import D5.S3.Quantum.Reduction.CoherentFlagPort

noncomputable section
open Matrix
open scoped BigOperators
namespace D5.S3.Quantum.Reduction.CanonicalFlagCompression
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Reduction.ProbeComponentRigidity
open D5.S3.Quantum.Reduction.CoherentFlagPort
variable {d q F : Type*} [Fintype d] [DecidableEq d]
  [Fintype q] [DecidableEq q] [Fintype F] [DecidableEq F]

/-- The canonical encoder lands in the classical direct-sum sectors on all
    matrix inputs. This is an algebraic codomain restriction, not fixed flag probabilities. -/
def ClassicalOutput (E : QuantumChannel d (F × q)) : Prop :=
  ∀ X : Matrix d d ℂ, ∀ f g : F, f ≠ g → ∀ i j : q,
    CStarMatrix.ofMatrix.symm
      (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) (f,i) (g,j) = 0

omit [Fintype d] [DecidableEq d] [DecidableEq q] [DecidableEq F] in
private theorem diagonal_decoder_action {b : Type*} [Fintype b]
    (R : b → Matrix d (F × q) ℂ) (Y : Matrix (F × q) (F × q) ℂ)
    (hY : ∀ f g : F, f ≠ g → ∀ i j : q, Y (f,i) (g,j) = 0) :
    (∑ b, R b * Y * (R b)ᴴ) =
      ∑ f, ∑ b, (R b).submatrix id (fun j => (f,j)) *
        Y.submatrix (fun i => (f,i)) (fun j => (f,j)) *
        ((R b).submatrix id (fun j => (f,j)))ᴴ := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Matrix.submatrix_apply, Function.id_def]
  have hfg (b : b) (g : F) (k : q) :
      (∑ f : F, ∑ l : q, R b i (f,l) * Y (f,l) (g,k) * star (R b j (g,k))) =
        ∑ l : q, R b i (g,l) * Y (g,l) (g,k) * star (R b j (g,k)) := by
    apply Finset.sum_eq_single g
    · intro f hf hne
      simp only [hY f g hne, mul_zero, zero_mul, Finset.sum_const_zero]
    · intro h
      exact (h (Finset.mem_univ g)).elim
  simp only [hfg]
  rw [Finset.sum_comm]

/-- Every actual canonical CPTP encoder with classical flag output and every
    canonical CPTP decoder yield the normalized rectangular finite Kraus port.
    The original composite agrees on every matrix, with the same actual flag. -/
theorem canonical_flag_port_factorization
    (E : QuantumChannel d (F × q)) (D : QuantumChannel (F × q) d)
    (hclass : ClassicalOutput E) :
    ∃ port : FlagPort d q F ((F × q) × d) (d × (F × q)),
      ∀ X : Matrix d d ℂ,
        CStarMatrix.ofMatrix.symm (D.toCompletelyPositiveMap
          (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) =
        ∑ k, port.kraus k * X * (port.kraus k)ᴴ := by
  let A := (krausRepresentation E.toCompletelyPositiveMap).1
  let R := (krausRepresentation D.toCompletelyPositiveMap).1
  have hA := (krausRepresentation E.toCompletelyPositiveMap).2
  have hR := (krausRepresentation D.toCompletelyPositiveMap).2
  have hnA := kraus_normalized_of_channel E A hA
  have hnR := kraus_normalized_of_channel D R hR
  let B : F → ((F × q) × d) → Matrix q d ℂ := fun f a i j => A a (f,i) j
  let S : F → (d × (F × q)) → Matrix d q ℂ := fun f b i j => R b i (f,j)
  have hb : (∑ f, ∑ a, (B f a)ᴴ * B f a) = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B]
    rw [Finset.sum_comm]
    simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type] using congrArg (fun M : Matrix d d ℂ => M i j) hnA
  have hs (f : F) : (∑ b, (S f b)ᴴ * S f b) = 1 := by
    ext i j
    simpa only [S, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Prod.mk.injEq, true_and] using
      congrArg (fun M : Matrix (F × q) (F × q) ℂ => M (f,i) (f,j)) hnR
  let port : FlagPort d q F ((F × q) × d) (d × (F × q)) :=
    ⟨B, S, hb, hs⟩
  refine ⟨port, fun X => ?_⟩
  let Y := CStarMatrix.ofMatrix.symm
    (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))
  have he : E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X) = CStarMatrix.ofMatrix Y := by
    exact CStarMatrix.ofMatrix.symm.injective (by simp only [Equiv.symm_apply_apply]; rfl)
  rw [he, hR]
  have hblock (f : F) : Y.submatrix (fun i => (f,i)) (fun j => (f,j)) =
      ∑ a, B f a * X * (B f a)ᴴ := by
    ext i j
    simp only [Matrix.submatrix_apply]
    dsimp only [Y]
    rw [hA]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B]
    rfl
  rw [diagonal_decoder_action R Y (hclass X)]
  change (∑ f, ∑ b, S f b * Y.submatrix (fun i => (f,i)) (fun j => (f,j)) *
    (S f b)ᴴ) = ∑ k, port.kraus k * X * (port.kraus k)ᴴ
  dsimp only [port]
  simp only [hblock, Matrix.mul_sum, Matrix.sum_mul, FlagPort.kraus,
    Fintype.sum_prod_type, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The component-dimension lower bound applies directly to arbitrary actual
    canonical CPTP encoders and decoders with classical flag outputs. -/
theorem canonical_flag_port_lower_bound {J : Type*}
    (E : QuantumChannel d (F × q)) (D : QuantumChannel (F × q) d)
    (hclass : ClassicalOutput E)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hprob : ∀ j (ρ : DensityState d),
      trace (probe (v j) * CStarMatrix.ofMatrix.symm
        (D.toCompletelyPositiveMap (E.toCompletelyPositiveMap ρ.1))) =
      trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) :
    ∀ j, Module.finrank ℂ (componentSpace v j) ≤ Fintype.card q := by
  obtain ⟨port, hp⟩ := canonical_flag_port_factorization E D hclass
  apply port_component_lower_bound port v hv
  intro j ρ
  rw [← hp]
  simpa only [Equiv.apply_symm_apply] using hprob j ρ

#print axioms canonical_flag_port_factorization
#print axioms canonical_flag_port_lower_bound
end D5.S3.Quantum.Reduction.CanonicalFlagCompression
