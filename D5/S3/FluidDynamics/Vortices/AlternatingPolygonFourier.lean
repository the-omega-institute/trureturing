/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete Fourier coordinates of the actual Cartesian alternating-polygon derivative. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes

/-! Complete paired Fourier coordinates, constructed from the canonical transform. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonFourier
open InverseChordCirculant AlternatingPolygonSpectrum AlternatingPolygonModes
open D5.S3.Quantum.Dynamics.PolygonalFourierCouplings

/-- Relabel the existing finite polygon, without changing its cyclic order. -/
def relabel (m : ℕ) [NeZero (2 * m)] :
    (Fin (2 * m) → ℂ) ≃ₗ[ℂ] (ZMod (2 * m) → ℂ) where
  toFun v j := v ((ZMod.finEquiv (2 * m)).symm j)
  invFun v j := v ((ZMod.finEquiv (2 * m)) j)
  left_inv v := by funext j; simp
  right_inv v := by funext j; simp
  map_add' v w := rfl
  map_smul' c v := rfl

/-- The canonical DFT, after the faithful cyclic relabeling. -/
def fourier (m : ℕ) [NeZero (2 * m)] :
    (Fin (2 * m) → ℂ) ≃ₗ[ℂ] (ZMod (2 * m) → ℂ) :=
  (relabel m).trans ZMod.dft

private theorem dft_circulant (N : ℕ) [NeZero N] (w v : ZMod N → ℂ) (q : ZMod N) :
    ZMod.dft ((Matrix.circulant w).mulVec v) q = ZMod.dft w q * ZMod.dft v q := by
  have ht (v : ZMod N → ℂ) (q : ZMod N) :
      (transform N).mulVec v q = ZMod.dft v q / (Real.sqrt N : ℂ) := by
    simp only [transform, Matrix.mulVec, dotProduct, ZMod.dft_apply, smul_eq_mul,
      Finset.sum_div, div_mul_eq_mul_div]
    congr 1
    funext j
    rw [mul_comm j q]
  have h := congrArg (fun A : Matrix (ZMod N) (ZMod N) ℂ => A.mulVec v q)
    (circulant_spectral N w)
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, ht] at h
  have hs : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos N)))
  apply (div_left_inj' hs).mp
  simpa only [D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.spectralValue,
    mul_div_assoc] using h

private theorem relabel_mulVec (m : ℕ) [NeZero (2 * m)]
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) (v : Fin (2 * m) → ℂ) :
    relabel m (A.mulVec v) =
      (Matrix.reindex (ZMod.finEquiv (2 * m)).toEquiv
        (ZMod.finEquiv (2 * m)).toEquiv A).mulVec (relabel m v) := by
  funext q
  change (A.mulVec v) ((ZMod.finEquiv (2 * m)).symm q) = _
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, relabel]
  exact ((ZMod.finEquiv (2 * m)).toEquiv.symm.sum_comp
    (fun j : Fin (2 * m) => A ((ZMod.finEquiv (2 * m)).symm q) j * v j)).symm

private theorem fourier_weights (m : ℕ) [NeZero (2 * m)]
    (v : Fin (2 * m) → ℂ) (q : ZMod (2 * m)) :
    fourier m (((weights m).map Complex.ofRealHom).mulVec v) q =
      (((((2 * m : ℕ) : ℝ) ^ 2 - 1) / 12 -
        (q.val : ℝ) * ((2 * m : ℕ) - q.val) / 2 : ℝ) : ℂ) * fourier m v q := by
  let e := ZMod.finEquiv (2 * m)
  have hW : Matrix.reindex e.toEquiv e.toEquiv ((weights m).map Complex.ofRealHom) =
      Matrix.circulant (fun l => (chordWeight (2 * m) l : ℂ)) := by
    ext i j
    change (weights m (e.symm i) (e.symm j) : ℂ) = _
    rw [spectrum_weights]
    change (chordWeight (2 * m) (e (e.symm i - e.symm j)) : ℂ) = _
    rw [map_sub]
    simp only [RingEquiv.apply_symm_apply]
    rfl
  change ZMod.dft (relabel m _) q = _
  rw [relabel_mulVec, hW, dft_circulant, chordWeight_dft]
  rfl

private theorem fourier_charge (m : ℕ) [NeZero (2 * m)]
    (v : Fin (2 * m) → ℂ) (q : ZMod (2 * m)) :
    fourier m (((chargeMatrix m).map Complex.ofRealHom).mulVec v) q =
      fourier m v (q + m) := by
  have hchar (j : ZMod (2 * m)) :
      ZMod.stdAddChar (-(j * (m : ZMod (2 * m)))) = (-1 : ℂ) ^ j.val := by
    calc
      _ = ZMod.stdAddChar (j.val • (-(m : ZMod (2 * m)))) := by
        congr 1
        simp [nsmul_eq_mul]
      _ = ZMod.stdAddChar (-(m : ZMod (2 * m))) ^ j.val :=
        AddChar.map_nsmul_eq_pow _ _ _
      _ = _ := by rw [AddChar.map_neg_eq_inv, half_character]; simp
  change ZMod.dft (relabel m _) q = ZMod.dft (relabel m v) (q + m)
  simp only [ZMod.dft_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change ZMod.stdAddChar (-(j * q)) *
    (((chargeMatrix m).map Complex.ofRealHom).mulVec v)
      ((ZMod.finEquiv (2 * m)).symm j) =
    ZMod.stdAddChar (-(j * (q + (m : ZMod (2 * m))))) * v ((ZMod.finEquiv (2 * m)).symm j)
  rw [chargeMatrix_diagonal, Matrix.diagonal_map (map_zero Complex.ofRealHom)]
  simp only [Matrix.mulVec_diagonal, Complex.ofRealHom_eq_coe,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  have hv : ((ZMod.finEquiv (2 * m)).symm j).val = j.val := by
    simpa only [RingEquiv.apply_symm_apply] using
      (D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories.fin_equiv_val
        (2 * m) ((ZMod.finEquiv (2 * m)).symm j)).symm
  rw [hv, pow_add, neg_one_sq, mul_one, mul_add, neg_add, AddChar.map_add_eq_mul, hchar]
  ring

private theorem fourier_block (m : ℕ) [NeZero (2 * m)] (c : ℝ)
    (v : Fin (2 * m) → ℂ) (q : ZMod (2 * m)) :
    fourier m (((((diagonalWeight m + c) • 1 - weights m) * chargeMatrix m).map
      Complex.ofRealHom).mulVec v) q =
      ((ell m q + c : ℝ) : ℂ) * fourier m v (q + m) := by
  have hsub (A B : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
      (A - B).map Complex.ofRealHom = A.map Complex.ofRealHom - B.map Complex.ofRealHom := by
    ext i j
    exact map_sub Complex.ofRealHom (A i j) (B i j)
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hsub, Matrix.sub_mulVec]
  have hscalar : (((diagonalWeight m + c) •
      (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)).map Complex.ofRealHom) =
      ((diagonalWeight m + c : ℝ) : ℂ) • 1 := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero Complex.ofRealHom),
      ← Matrix.smul_one_eq_diagonal]
    rfl
  rw [hscalar, Matrix.smul_mulVec, Matrix.one_mulVec, map_sub, map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [fourier_weights, fourier_charge]
  have hc : ((diagonalWeight m + c : ℝ) : ℂ) -
      (((((2 * m : ℕ) : ℝ) ^ 2 - 1) / 12 -
        (q.val : ℝ) * ((2 * m : ℕ) - q.val) / 2 : ℝ) : ℂ) =
      ((ell m q + c : ℝ) : ℂ) := by
    simp only [diagonalWeight, ell, Nat.cast_mul, Nat.cast_ofNat,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  rw [← sub_mul, hc]

/-- Paired Fourier coordinates. The tangential frequency is shifted by m. -/
def frequencyCoordinates (m : ℕ) [NeZero (2 * m)] :
    (Fin (2 * m) ⊕ Fin (2 * m) → ℂ) ≃ₗ[ℂ] (ZMod (2 * m) → ℂ × ℂ) where
  toFun v q := (fourier m (fun j => v (.inl j)) q,
    fourier m (fun j => v (.inr j)) (q + m))
  invFun w p := match p with
    | .inl j => (fourier m).symm (fun q => (w q).1) j
    | .inr j => (fourier m).symm (fun q => (w (q - m)).2) j
  left_inv v := by
    funext p
    cases p with
    | inl j => exact congrFun ((fourier m).symm_apply_apply _) j
    | inr j =>
      simp only [sub_add_cancel]
      exact congrFun ((fourier m).symm_apply_apply _) j
  right_inv w := by
    funext q
    apply Prod.ext
    · exact congrFun ((fourier m).apply_symm_apply _) q
    · simpa only [add_sub_cancel_right] using
        congrFun ((fourier m).apply_symm_apply (fun q => (w (q - m)).2)) (q + m)
  map_add' v w := by
    funext q
    apply Prod.ext <;> simp only [← Pi.add_def, map_add, Pi.add_apply, Prod.fst_add, Prod.snd_add]
  map_smul' c v := by
    funext q
    apply Prod.ext <;> simp only [← Pi.smul_def, map_smul, Pi.smul_apply,
      Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]

/-- The actual radial/tangential block action in the complete Fourier coordinates. -/
theorem frequency_block (m : ℕ) [NeZero (2 * m)]
    (v : Fin (2 * m) ⊕ Fin (2 * m) → ℂ) :
    frequencyCoordinates m
      (((Matrix.fromBlocks 0 (blockB m) (blockC m) 0).map Complex.ofRealHom).mulVec v) =
      pairedOperator (fun q => (ell m q : ℂ)) (fun q => (ell m (q + m) + 1 : ℝ))
        (frequencyCoordinates m v) := by
  have hshift (q : ZMod (2 * m)) : q + m + m = q := by
    have hm : (m : ZMod (2 * m)) + m = 0 := by
      rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
    rw [add_assoc, hm, add_zero]
  have hb : ∀ q, fourier m (((blockB m).map Complex.ofRealHom).mulVec
      (fun j => v (.inr j))) q = (ell m q : ℂ) *
        fourier m (fun j => v (.inr j)) (q + m) := by
    intro q
    simpa only [blockB, add_zero] using fourier_block m 0 (fun j => v (.inr j)) q
  have hc : ∀ q, fourier m (((blockC m).map Complex.ofRealHom).mulVec
      (fun j => v (.inl j))) q = ((ell m q + 1 : ℝ) : ℂ) *
        fourier m (fun j => v (.inl j)) (q + m) := by
    intro q
    exact fourier_block m 1 (fun j => v (.inl j)) q
  have hzero : (0 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ).map
      Complex.ofRealHom = 0 := by ext; simp
  rw [Matrix.fromBlocks_map, hzero, Matrix.fromBlocks_mulVec]
  funext q
  apply Prod.ext
  · change fourier m (0 *ᵥ (v ∘ Sum.inl) +
        ((blockB m).map Complex.ofRealHom) *ᵥ (v ∘ Sum.inr)) q =
      (ell m q : ℂ) * fourier m (fun j => v (.inr j)) (q + m)
    simpa only [Matrix.zero_mulVec, zero_add, Function.comp_def] using hb q
  · change fourier m (((blockC m).map Complex.ofRealHom) *ᵥ (v ∘ Sum.inl) +
        0 *ᵥ (v ∘ Sum.inr)) (q + m) =
      ((ell m (q + m) + 1 : ℝ) : ℂ) * fourier m (fun j => v (.inl j)) q
    simpa only [Matrix.zero_mulVec, add_zero, Function.comp_def, hshift] using hc (q + m)

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonFourier
