/- GID: D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/HoggarSicCompoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.claim; result=D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.result; claim=D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.claim
   digest: Eight orthogonal Hoggar fiducials give a SIC-compound in complex dimension eight. -/

import D5.S3.Quantum.Measurement.HoggarSicSumNegativity

set_option linter.style.longLine false

open scoped BigOperators
open D5.S3.Quantum.Measurement.HoggarSicSumNegativity (bitSign)

namespace D5.S3.Quantum.Measurement.HoggarSicCompoundRefutation

set_option maxRecDepth 4000

private noncomputable def phase (z b : Fin 8) : ℂ :=
  GaussianInt.toComplex (bitSign z.val b.val)

/-- The three-qubit Pauli action, with the shift applied before the parity sign. -/
noncomputable def pauli (x z : Fin 8) (u : Fin 8 → ℂ) (b : Fin 8) : ℂ :=
  phase z (b ^^^ x) * u (b ^^^ x)

/-- Equation (1) in dimension eight, indexed by the 64 Pauli labels. -/
def IsSIC (φ : (Fin 8 × Fin 8) → Fin 8 → ℂ) : Prop :=
  ∀ j l, Complex.normSq (star (φ j) ⬝ᵥ φ l) =
    (8 * (if j = l then 1 else 0) + 1) / 9

/-- Nonexistence of a compound whose eight SICs are three-qubit Pauli orbits. -/
def claim : Prop :=
  ¬ ∃ f : Fin 8 → Fin 8 → ℂ,
    (∀ k, IsSIC (fun j => pauli j.1 j.2 (f k))) ∧
    (∀ j : Fin 8 × Fin 8, ∀ k l,
      star (pauli j.1 j.2 (f k)) ⬝ᵥ pauli j.1 j.2 (f l) =
        if k = l then 1 else 0)

private def w : Fin 8 → Fin 8 → GaussianInt := ![
  ![⟨-1,2⟩,1,1,1,1,1,1,1],
  ![1,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩,⟨1,-1⟩,0,0,0],
  ![1,⟨0,1⟩,⟨1,-1⟩,0,⟨0,1⟩,⟨0,1⟩,0,0],
  ![1,⟨1,-1⟩,⟨0,1⟩,0,⟨0,1⟩,0,⟨0,1⟩,0],
  ![1,-1,-1,1,-1,1,1,⟨1,2⟩],
  ![0,0,0,⟨1,1⟩,⟨0,1⟩,⟨0,-1⟩,⟨0,-1⟩,-1],
  ![0,0,1,-1,0,⟨1,-1⟩,-1,⟨0,1⟩],
  ![0,1,0,-1,0,-1,⟨1,-1⟩,⟨0,1⟩]]

private def r : Fin 8 → ℤ := ![12,6,6,6,12,6,6,6]

private def pauliG (x z : Fin 8) (u : Fin 8 → GaussianInt) (b : Fin 8) : GaussianInt :=
  bitSign z.val (b ^^^ x).val * u (b ^^^ x)

private theorem gram : ∀ k l : Fin 8,
    (∑ b : Fin 8, star (w k b) * w l b) =
      if k = l then (r k : GaussianInt) else 0 := by
  decide +kernel

private theorem self_overlap : ∀ k x z : Fin 8,
    Zsqrtd.norm (∑ b : Fin 8, star (w k b) * pauliG x z (w k) b) =
      if x = 0 ∧ z = 0 then r k ^ 2 else r k ^ 2 / 9 := by
  decide +kernel

private theorem sign_laws : ∀ z t b : Fin 8,
    star (bitSign z.val b.val) = bitSign z.val b.val ∧
    bitSign z.val b.val * bitSign z.val b.val = 1 ∧
    bitSign z.val (b ^^^ t).val = bitSign z.val b.val * bitSign z.val t.val ∧
    bitSign (z ^^^ t).val b.val = bitSign z.val b.val * bitSign t.val b.val := by
  decide +kernel

private theorem phase_laws (z t b : Fin 8) :
    star (phase z b) = phase z b ∧ phase z b * phase z b = 1 ∧
    phase z (b ^^^ t) = phase z b * phase z t ∧
    phase (z ^^^ t) b = phase z b * phase t b := by
  obtain ⟨hc, hs, ha, hb⟩ := sign_laws z t b
  exact ⟨by simpa only [phase.eq_1, GaussianInt.toComplex_star, Complex.star_def] using
      congrArg GaussianInt.toComplex hc,
    by simpa only [phase.eq_1, map_mul, map_one] using congrArg GaussianInt.toComplex hs,
    by simpa only [phase.eq_1, map_mul] using congrArg GaussianInt.toComplex ha,
    by simpa only [phase.eq_1, map_mul] using congrArg GaussianInt.toComplex hb⟩

private theorem pauli_mul (x z y t : Fin 8) (u : Fin 8 → ℂ) :
    pauli x z (pauli y t u) =
      fun b => phase z y * pauli (x ^^^ y) (z ^^^ t) u b := by
  funext b
  simp only [pauli.eq_1, xor_assoc (α := Fin (2 ^ 3))]
  rw [(phase_laws z t (b ^^^ (x ^^^ y))).2.2.2]
  have hs : phase z (b ^^^ x) =
      phase z (b ^^^ (x ^^^ y)) * phase z y := by
    rw [← (phase_laws z y (b ^^^ (x ^^^ y))).2.2.1]
    congr 1
    calc
      b ^^^ x = ((b ^^^ x) ^^^ y) ^^^ y :=
        (xor_cancel_right (α := Fin (2 ^ 3)) (b ^^^ x) y).symm
      _ = (b ^^^ (x ^^^ y)) ^^^ y :=
        congrArg (fun q : Fin 8 => q ^^^ y) (xor_assoc (α := Fin (2 ^ 3)) b x y)
  rw [hs]
  ring

private theorem pauli_inner (x z : Fin 8) (u v : Fin 8 → ℂ) :
    star (pauli x z u) ⬝ᵥ pauli x z v = star u ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply, pauli.eq_1, star_mul]
  calc
    _ = ∑ b : Fin 8, star (u (b ^^^ x)) * v (b ^^^ x) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [(phase_laws z 0 (b ^^^ x)).1]
      calc
        _ = (phase z (b ^^^ x) * phase z (b ^^^ x)) *
            (star (u (b ^^^ x)) * v (b ^^^ x)) := by ring
        _ = _ := by rw [(phase_laws z 0 (b ^^^ x)).2.1, one_mul]
    _ = _ := by
      exact Fintype.sum_bijective (fun b : Fin 8 => b ^^^ x)
        (xor_left_involutive (α := Fin (2 ^ 3)) x).bijective
        _ _ (fun _ => rfl)

private theorem pair_overlap (x z y t : Fin 8) (u : Fin 8 → ℂ) :
    Complex.normSq (star (pauli x z u) ⬝ᵥ pauli y t u) =
      Complex.normSq (star u ⬝ᵥ pauli (x ^^^ y) (z ^^^ t) u) := by
  have hi := pauli_inner x z u (pauli (x ^^^ y) (z ^^^ t) u)
  have hx : (x ^^^ (x ^^^ y) : Fin 8) = y :=
    xor_cancel_left (α := Fin (2 ^ 3)) x y
  have hz : (z ^^^ (z ^^^ t) : Fin 8) = t :=
    xor_cancel_left (α := Fin (2 ^ 3)) z t
  rw [pauli_mul, hx, hz] at hi
  have hs : star (pauli x z u) ⬝ᵥ
      (fun b => phase z (x ^^^ y) * pauli y t u b) =
        phase z (x ^^^ y) * (star (pauli x z u) ⬝ᵥ pauli y t u) := by
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hs] at hi
  have hn : Complex.normSq (phase z (x ^^^ y)) = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def,
      (phase_laws z 0 (x ^^^ y)).1, (phase_laws z 0 (x ^^^ y)).2.1]
    rfl
  have he := congrArg Complex.normSq hi
  rwa [Complex.normSq_mul, hn, one_mul] at he


private theorem r_cases : ∀ k : Fin 8, r k = 6 ∨ r k = 12 := by
  decide +kernel

private noncomputable def raw (k b : Fin 8) : ℂ := GaussianInt.toComplex (w k b)

private noncomputable def fid (k b : Fin 8) : ℂ :=
  raw k b / (Real.sqrt (r k : ℝ) : ℂ)

private theorem cast_dot (u v : Fin 8 → GaussianInt) :
    star (fun b => GaussianInt.toComplex (u b)) ⬝ᵥ
        (fun b => GaussianInt.toComplex (v b)) =
      GaussianInt.toComplex (∑ b : Fin 8, star (u b) * v b) := by
  change _ = GaussianInt.toComplex (star u ⬝ᵥ v)
  rw [RingHom.map_dotProduct]
  congr 1
  funext b
  simp only [Function.comp_def, Pi.star_apply, GaussianInt.toComplex_star,
    Complex.star_def]

private theorem cast_pauli (x z : Fin 8) (u : Fin 8 → GaussianInt) :
    pauli x z (fun b => GaussianInt.toComplex (u b)) =
      fun b => GaussianInt.toComplex (pauliG x z u b) := by
  funext b
  simp only [pauli.eq_1, phase.eq_1, pauliG.eq_1, map_mul]

private theorem raw_gram (k l : Fin 8) :
    star (raw k) ⬝ᵥ raw l = if k = l then (r k : ℂ) else 0 := by
  change star (fun b => GaussianInt.toComplex (w k b)) ⬝ᵥ
    (fun b => GaussianInt.toComplex (w l b)) = _
  rw [cast_dot, gram]
  split_ifs <;> simp only [map_intCast, map_zero]

private theorem raw_self (k x z : Fin 8) :
    Complex.normSq (star (raw k) ⬝ᵥ pauli x z (raw k)) =
      if x = 0 ∧ z = 0 then (r k : ℝ) ^ 2 else (r k : ℝ) ^ 2 / 9 := by
  change Complex.normSq (star (fun b => GaussianInt.toComplex (w k b)) ⬝ᵥ
    pauli x z (fun b => GaussianInt.toComplex (w k b))) = _
  rw [cast_pauli, cast_dot, ← GaussianInt.intCast_real_norm, self_overlap]
  rcases r_cases k with h | h <;> split_ifs <;> norm_num [h]

private theorem divide_dot (u v : Fin 8 → ℂ) (a b : ℝ) :
    star (fun i => u i / (a : ℂ)) ⬝ᵥ (fun i => v i / (b : ℂ)) =
      (star u ⬝ᵥ v) / ((a : ℂ) * (b : ℂ)) := by
  simp only [dotProduct, Pi.star_apply, star_div₀, Complex.star_def,
    Complex.conj_ofReal, div_mul_div_comm, Finset.sum_div]

private theorem pauli_div (x z : Fin 8) (u : Fin 8 → ℂ) (a : ℝ) :
    pauli x z (fun b => u b / (a : ℂ)) =
      fun b => pauli x z u b / (a : ℂ) := by
  funext b
  simp only [pauli.eq_1, mul_div_assoc]

private theorem r_positive (k : Fin 8) : 0 < (r k : ℝ) := by
  rcases r_cases k with h | h <;> norm_num [h]

private theorem sqrt_product (k : Fin 8) :
    (Real.sqrt (r k : ℝ) : ℂ) * (Real.sqrt (r k : ℝ) : ℂ) = (r k : ℂ) := by
  rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (le_of_lt (r_positive k))]
  norm_cast

private theorem fid_inner (k l : Fin 8) :
    star (fid k) ⬝ᵥ fid l = if k = l then 1 else 0 := by
  change star (fun b => raw k b / (Real.sqrt (r k : ℝ) : ℂ)) ⬝ᵥ
    (fun b => raw l b / (Real.sqrt (r l : ℝ) : ℂ)) = _
  rw [divide_dot, raw_gram]
  by_cases h : k = l
  · subst l
    simp only
    rw [sqrt_product]
    exact div_self (by exact_mod_cast ne_of_gt (r_positive k))
  · simp only [if_neg h, zero_div]

private theorem fid_self (k x z : Fin 8) :
    Complex.normSq (star (fid k) ⬝ᵥ pauli x z (fid k)) =
      if x = 0 ∧ z = 0 then 1 else 1 / 9 := by
  change Complex.normSq (star (fun b => raw k b / (Real.sqrt (r k : ℝ) : ℂ)) ⬝ᵥ
    pauli x z (fun b => raw k b / (Real.sqrt (r k : ℝ) : ℂ))) = _
  rw [pauli_div, divide_dot, sqrt_product, Complex.normSq_div,
    Complex.normSq_intCast, raw_self]
  have hr : (r k : ℝ) ≠ 0 := ne_of_gt (r_positive k)
  split_ifs <;> field_simp [hr]

/-- Eight Pauli SICs are simultaneously partitioned into 64 orthonormal bases. -/
theorem result : ¬ claim := by
  intro h
  apply h
  refine ⟨fid, ?_, ?_⟩
  · intro k j l
    by_cases he : j = l
    · subst l
      rw [pauli_inner, fid_inner, if_pos rfl]
      norm_num
    · rw [pair_overlap, fid_self]
      have hn : ¬ (j.1 ^^^ l.1 = 0 ∧ j.2 ^^^ l.2 = 0) := by
        intro hp
        apply he
        exact Prod.ext ((xor_eq_zero_iff (α := Fin (2 ^ 3))).mp hp.1)
          ((xor_eq_zero_iff (α := Fin (2 ^ 3))).mp hp.2)
      rw [if_neg hn, if_neg he]
      norm_num
  · intro j k l
    rw [pauli_inner, fid_inner]

end D5.S3.Quantum.Measurement.HoggarSicCompoundRefutation
