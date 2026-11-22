/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedFiniteBridge
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Replay.existsUnique_zero; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Bounds.row_bounds
   digest: Exact compatibility of the finite integer evaluator with the fixed-point soundness formulas. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedFinite
import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedReplaySoundness

namespace ChirpedFinite

open scoped BigOperators

noncomputable def decodeDyadic (x : Dyadic) : ℝ :=
  (x.1 : ℝ) * (2 : ℝ) ^ x.2

theorem decodeDyadic_ratio (x : Dyadic) :
    decodeDyadic x = (dyadicNumerator x : ℝ) / (dyadicDenominator x : ℝ) := by
  have h : (x.2.toNat : ℤ) - ((-x.2).toNat : ℤ) = x.2 := by omega
  simp only [decodeDyadic, dyadicNumerator, dyadicDenominator, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, mul_div_assoc]
  rw [← zpow_natCast_sub_natCast₀ (by norm_num : (2 : ℝ) ≠ 0), h]

theorem root_error {n : ℕ} (j : Fin n) :
    ‖ChirpedReplay.IntComplex.decode scale (root n j.val) -
      ChirpedReplay.unitPhase (2 * Real.pi * (j.val : ℝ) / n)‖ ≤ 45 / (scale : ℝ) :=
  ChirpedReplay.root_error j

theorem cayley_error (x : Dyadic) (s : ℤ) :
    ‖ChirpedReplay.IntComplex.decode scale (cayley x s).1 -
      ChirpedReplay.cayley (decodeDyadic x) s‖ ≤ 2 / (scale : ℝ) ∧
    ‖ChirpedReplay.IntComplex.decode scale (cayley x s).2 -
      ChirpedReplay.cayleySlope (decodeDyadic x) s‖ ≤ 2 / (scale : ℝ) := by
  rw [decodeDyadic_ratio]
  exact ChirpedReplay.cayley_error (dyadicNumerator x) (dyadicDenominator x) s (dyadicDenominator_pos x)

noncomputable def exactRoot (n j : ℕ) : ℂ :=
  ChirpedReplay.unitPhase (2 * Real.pi * (j : ℝ) / n)

noncomputable def exactCoefficient (n e d : ℕ) (orbit : List ℕ) : ℂ :=
  sumRange orbit.length (fun j => exactRoot n ((e + d * orbit.getD j 0) % n))

noncomputable def exactSeedValue (n : ℕ) (phases : ℕ → ℂ) (d : ℕ) : Seed → ℂ
  | .chirped layout =>
    let e := chirpExponent n layout d
    (exactRoot n (e % n) + sumRange layout.orbits.length (fun j =>
      exactCoefficient n e d (layout.orbits.getD j []) * phases (layout.first + j))) / (n : ℂ)
  | .constantSpectrum k => (if d = 0 then 1 else 0) + (phases k - 1) / (n : ℂ)

noncomputable def exactSeedSlope (n : ℕ) (slopes : ℕ → ℂ) (d j : ℕ) : Seed → ℂ
  | .chirped layout =>
    if layout.first ≤ j ∧ j < layout.first + layout.orbits.length then
      let e := chirpExponent n layout d
      exactCoefficient n e d (layout.orbits.getD (j - layout.first) []) * slopes j / (n : ℂ)
    else 0
  | .constantSpectrum k => if j = k then slopes j / (n : ℂ) else 0

/-- Use the same row selector and left-column permutation for both arithmetic and analytic values. -/
def selectRows {m n : ℕ} {K : Type*} (inverse : ℕ) (pick : Fin m → Constraint)
    (v : ℕ → ℕ → K) (dv : ℕ → ℕ → ℕ → K) : ChirpedReplay.CorrelationRows (Fin m) n K where
  left i d := v (pick i).left (leftColumn n inverse (pick i) d.val)
  right i d := v (pick i).right d.val
  leftSlope i j d := dv (pick i).left (leftColumn n inverse (pick i) d.val) j.val
  rightSlope i j d := dv (pick i).right d.val j.val

theorem selectRows_residual {m n : ℕ} (inverse : ℕ) (pick : Fin m → Constraint)
    (v : ℕ → ℕ → Gaussian) (dv : ℕ → ℕ → ℕ → Gaussian) (imag : Fin m → Bool) (i : Fin m) :
    (selectRows (n := n) inverse pick v dv).residual imag i =
      component (imag i) (sumRange n (corrTerm n inverse (pick i) v)) :=
  congrArg (component (imag i)) (sumRange_fin n (corrTerm n inverse (pick i) v))

theorem selectRows_jacobian {m n : ℕ} (inverse : ℕ) (pick : Fin m → Constraint)
    (v : ℕ → ℕ → Gaussian) (dv : ℕ → ℕ → ℕ → Gaussian) (imag : Fin m → Bool) (i j : Fin m) :
    (selectRows (n := n) inverse pick v dv).jacobian imag i j =
      component (imag i) (sumRange n (jacTerm n inverse (pick i) v dv j.val)) := by
  have h := sumRange_fin n (jacTerm n inverse (pick i) v dv j.val)
  simp only [jacTerm, Finset.sum_add_distrib] at h
  exact congrArg (component (imag i)) h

theorem dyadicExponent_eq {m : ℕ} (y : Matrix (Fin m) (Fin m) Dyadic) (exponent : ℕ)
    (hle : ∀ i j, (-(y i j).2).toNat ≤ exponent) (i j : Fin m)
    (heq : (-(y i j).2).toNat = exponent) :
    ChirpedReplay.dyadicExponent y = exponent := by
  apply le_antisymm
  · unfold ChirpedReplay.dyadicExponent
    exact Finset.sup_le (fun i _ => Finset.sup_le (fun j _ => hle i j))
  · rw [← heq]
    exact (Finset.le_sup (f := fun j => (-(y i j).2).toNat) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun i => Finset.univ.sup fun j => (-(y i j).2).toNat)
        (Finset.mem_univ i))

theorem rowWeight_fin (m : ℕ) (a : ℕ → ℕ → ℤ) (i : Fin m) :
    ChirpedReplay.rowWeight (fun (j k : Fin m) => a j.val k.val) i = rowWeight m a i.val :=
  sumRange_fin m (fun j => |a i.val j|)

theorem stepRow_fin (n m : ℕ) (a : ℕ → ℕ → ℤ) (f : ℕ → ℤ) (i : Fin m) :
    ChirpedReplay.stepRow scale n (fun (j k : Fin m) => a j.val k.val) (fun j => f j.val) i =
      stepRow n m a f i.val := by
  simp only [ChirpedReplay.stepRow, stepRow, rowWeight_fin]
  rw [sumRange_fin m (fun j => a i.val j * f j)]

theorem defectRow_fin (D : ℤ) (n m : ℕ) (a j : ℕ → ℕ → ℤ) (i : Fin m) :
    ChirpedReplay.defectRow D scale n
      (fun (k l : Fin m) => a k.val l.val) (fun (k l : Fin m) => j k.val l.val) i =
      defectRow (D * scale ^ 2) n m a j i.val := by
  simp only [ChirpedReplay.defectRow, defectRow, rowWeight_fin, Fintype.card_fin]
  congr 1
  refine Eq.trans ?_ (sumRange_fin m (defectTerm (D * scale ^ 2) m a j i.val))
  apply Finset.sum_congr rfl
  intro k _
  simp only [ChirpedReplay.denominator, defectTerm, Fin.ext_iff]
  rw [sumRange_fin m (fun l => a i.val l * j l k.val)]

end ChirpedFinite
