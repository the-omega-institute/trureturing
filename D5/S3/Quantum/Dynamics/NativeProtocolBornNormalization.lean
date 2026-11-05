/- GID: D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeProtocolBornNormalization
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Complete original protocol trees conserve Born mass at every position cut. -/

import D5.S3.Quantum.Dynamics.NativeProtocolGraft

/-! Physical normalization of the complete original native protocol tree. -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization
open D5.S3.Quantum.Dynamics.NativeProtocolGraft
open D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree
open D5.S3.Quantum.Dynamics.NativeProtocolGraft.Actual

private theorem block_orthogonal : a * star b + b * star c = 0 := by
  have hs : t + t^2 = 1 := by linear_combination Coeff.t_sq
  have hz := Coeff.zeta_norm
  have he : a * star b + b * star c =
      (zeta * star zeta) * beta^3 *
        ((star zeta - 1) + (zeta - 1) +
          (zeta - 1) * (star zeta - 1) * (t + t^2)) := by
    simp only [a, b, c, star_mul, star_add, star_sub, star_one, star_pow,
      star_t, star_beta]
    ring
  rw [he, hs, hz]
  linear_combination beta^3 * hz

private theorem block_energy (x y : ℂ) :
    Complex.normSq (a*x+b*y) + Complex.normSq (b*x+c*y) =
      Complex.normSq x + Complex.normSq y := by
  have ha : a * star a + b * star b = 1 := by
    rw [a_norm, b_norm]
    linear_combination Coeff.t_sq
  have hc : b * star b + c * star c = 1 := by
    rw [b_norm, c_norm]
    linear_combination Coeff.t_sq
  have ho := block_orthogonal
  have ho' : star a * b + star b * c = 0 := by
    simpa only [star_add, star_mul, star_star, star_zero, mul_comm] using congrArg star ho
  apply Complex.ofReal_injective
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self, ← Complex.star_def,
    star_add, star_mul]
  linear_combination (star x*x)*ha + (star y*y)*hc + (star y*x)*ho +
    (star x*y)*ho'

private theorem gate_action (j : Address) (w : Basis → ℂ) (z : Basis) :
    (gate j).mulVec w z =
      if z (left j) then (if z (right j) then zeta^2 * w z else zeta * w z)
      else if z (right j) then zeta * w z
      else if z (center j) then b * w (NativeProtocolGraft.flip (center j) z) + c * w z
      else a * w z + b * w (NativeProtocolGraft.flip (center j) z) := by
  simp only [gate, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, Coeff.p_action]
  have ht : Coeff.evalO t Coeff.t_sq Coeff.tau = t := by
    simp [Coeff.evalO, Coeff.tau]
  cases hl : z (left j) <;> cases hr : z (right j) <;> cases hc : z (center j) <;>
    simp [Coeff.diagonal, Coeff.active, hl, hr, hc, map_pow, ht, a, b, c] <;> ring

private theorem gate_pair (j : Address) (w : Basis → ℂ) (z : Basis) :
    Complex.normSq ((gate j).mulVec w z) +
      Complex.normSq ((gate j).mulVec w (NativeProtocolGraft.flip (center j) z)) =
      Complex.normSq (w z) + Complex.normSq (w (NativeProtocolGraft.flip (center j) z)) := by
  have hf : NativeProtocolGraft.flip (center j) z (center j) = !(z (center j)) := by
    simp [NativeProtocolGraft.flip]
  have hl : NativeProtocolGraft.flip (center j) z (left j) = z (left j) := by
    apply Function.update_of_ne
    intro h
    have hh := congrArg Fin.val h
    simp [left, center] at hh
  have hr : NativeProtocolGraft.flip (center j) z (right j) = z (right j) := by
    apply Function.update_of_ne
    intro h
    have hh := congrArg Fin.val h
    simp [right, center] at hh
  have hz : Complex.normSq zeta = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self]
    simpa only [← Complex.star_def, mul_comm, Complex.ofReal_one] using Coeff.zeta_norm
  rw [gate_action, gate_action]
  simp only [hl, hr, hf, Coeff.flip_flip]
  cases hzl : z (left j) <;> cases hzr : z (right j) <;> cases hzc : z (center j) <;>
    simp only [hzl, hzr, hzc, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true]
  all_goals first
    | exact block_energy _ _
    | simpa only [add_comm] using block_energy (w (NativeProtocolGraft.flip (center j) z)) (w z)
    | simp only [map_mul, map_pow, hz, one_pow, one_mul]

private theorem gate_energy (j : Address) (w : Basis → ℂ) :
    Coeff.energy ((gate j).mulVec w) = Coeff.energy w := by
  classical
  have h := congrArg (fun f : Basis → ℝ => ∑ z, f z) (funext (gate_pair j w))
  simp only [Finset.sum_add_distrib] at h
  have hg := Coeff.flip_sum (center j) (fun z => Complex.normSq ((gate j).mulVec w z))
  have hw := Coeff.flip_sum (center j) (fun z => Complex.normSq (w z))
  rw [hg, hw] at h
  dsimp [Coeff.energy]
  linarith

private theorem power_energy (j : Address) (n : ℕ) (w : Basis → ℂ) :
    Coeff.energy ((gate j ^ n).mulVec w) = Coeff.energy w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, gate_energy]

private theorem call_energy (j : Address) (d : Direction) (w : Basis → ℂ) :
    Coeff.energy ((callMatrix j d).mulVec w) = Coeff.energy w := by
  cases d
  · exact gate_energy j w
  · exact power_energy j 9 w

private theorem measurement_energy {n : ℕ} (select : Basis → Fin n)
    (w : Basis → ℂ) :
    (∑ o, Coeff.energy ((projector select o).mulVec w)) = Coeff.energy w := by
  classical
  unfold Coeff.energy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [projector, Matrix.mulVec_diagonal, apply_ite]

/-- Conservation for arbitrary incoming vectors, proved on the original
finite tree with every outcome and its own continuation retained. -/
private theorem whole_tree_energy {L : Type} (T : NativeProtocolGraft.Tree L) (w : Basis → ℂ) :
    (∑ p : Path T, Coeff.energy ((operator T p).mulVec w)) = Coeff.energy w := by
  classical
  induction T generalizing w with
  | leaf l =>
    change (∑ _p : Unit, Coeff.energy ((1 : Mat).mulVec w)) = Coeff.energy w
    simp
  | call j d U ih =>
    change (∑ p : Path U, Coeff.energy
      ((operator U p * callMatrix j d).mulVec w)) = _
    simp only [← Matrix.mulVec_mulVec]
    rw [ih, call_energy]
  | measure n select U ih =>
    change (∑ p : (o : Fin n) × Path (U o), Coeff.energy
      ((operator (U p.1) p.2 * projector select p.1).mulVec w)) = _
    simp only [← Matrix.mulVec_mulVec]
    rw [Fintype.sum_sigma]
    simp_rw [ih]
    exact measurement_energy select w

/-- Computational coordinates on precisely the selected original positions. -/
abbrev CutBasis (I : Finset (Fin 16)) := {i : Fin 16 // i ∈ I} → Bool
abbrev CutRest (I : Finset (Fin 16)) := {i : Fin 16 // i ∉ I} → Bool

def splitAt (I : Finset (Fin 16)) : Basis ≃ CutBasis I × CutRest I :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ I) (fun _ => Bool)

/-- The original branch vector reduced at the actual position subset. -/
def cutReduced (I : Finset (Fin 16)) (v : Basis → ℂ) :
    Matrix (CutBasis I) (CutBasis I) ℂ :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
    (Matrix.vecMulVec (v ∘ (splitAt I).symm) (star (v ∘ (splitAt I).symm)))

/-- Sum of original unnormalized branch reductions over the acquired paths. -/
def eventCut {L : Type} (T : NativeProtocolGraft.Tree L) (I : Finset (Fin 16))
    (event : Path T → Bool) : Matrix (CutBasis I) (CutBasis I) ℂ :=
  ∑ p, if event p then cutReduced I ((operator T p).mulVec omega0) else 0

private theorem cutReduced_trace (I : Finset (Fin 16)) (v : Basis → ℂ) :
    (cutReduced I v).trace = (Coeff.energy v : ℂ) := by
  rw [cutReduced,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply,
    Function.comp_apply, Pi.star_apply, Coeff.energy]
  rw [← (splitAt I).sum_comp]
  simp only [Equiv.symm_apply_apply, Complex.ofReal_sum,
    Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem event_mass_energy {L : Type} (T : NativeProtocolGraft.Tree L)
    (event : Path T → Bool) :
    eventMass T (historyEvent event) =
      ∑ p, if event p then Coeff.energy ((operator T p).mulVec omega0) else 0 := by
  unfold eventMass historyEvent mass
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : event p
  · simp [he, Coeff.energy]
  · simp [he]

private theorem eventCut_trace {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (eventCut T I event).trace = (eventMass T (historyEvent event) : ℂ) := by
  rw [event_mass_energy, eventCut, Matrix.trace_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : event p <;> simp [he, cutReduced_trace]

private theorem eventCut_positive {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (eventCut T I event).PosSemidef := by
  classical
  unfold eventCut
  apply Matrix.posSemidef_sum
  intro p _
  split_ifs
  · exact D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star _)
  · exact Matrix.PosSemidef.zero

/-- The original complete Born law and the raw trace of the same acquired
history event at every original position cut, without normalization premises. -/
theorem original_complete_born_law {L : Type} (T : NativeProtocolGraft.Tree L)
    (event : Path T → Bool) (I : Finset (Fin 16)) :
    (∑ p, ∑ z, mass T p z) = 1 ∧
    (0 ≤ eventMass T (historyEvent event) ∧ eventMass T (historyEvent event) ≤ 1) ∧
    (eventCut T I event).PosSemidef ∧
    (eventCut T I event).trace = (eventMass T (historyEvent event) : ℂ) := by
  classical
  have ht : (∑ p, ∑ z, mass T p z) = 1 := by
    change (∑ p, Coeff.energy ((operator T p).mulVec omega0)) = 1
    rw [whole_tree_energy]
    simp [Coeff.energy, omega0]
  have hn : 0 ≤ eventMass T (historyEvent event) := by
    unfold eventMass
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro z _
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl
  have hb : eventMass T (historyEvent event) ≤ ∑ p, ∑ z, mass T p z := by
    unfold eventMass
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro z _
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _
  exact ⟨ht, ⟨hn, hb.trans_eq ht⟩, eventCut_positive T I event, eventCut_trace T I event⟩

#print axioms original_complete_born_law
end D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization
