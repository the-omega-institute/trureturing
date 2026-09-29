/- GID: D5/S3/Quantum/Entanglement/FiniteSectorFlatFeasibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteSectorFlatFeasibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact flat basis feasibility at arbitrary positive sector ranks. -/

import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open SectorSchmidtEncoding
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

variable {Sector : Type u} [Fintype Sector] [DecidableEq Sector]

set_option maxHeartbeats 40000000 in
/-- Flat basis output is feasible exactly at positive integer sector-rank multiples. -/
theorem flat_feasibility : FlatFeasibilityClaim (Sector := Sector) := by
  classical
  have hFlatNecessity {Target E F : Type u} [Fintype Target] [DecidableEq Target]
      [Fintype E] [DecidableEq E]
      [Fintype F] [DecidableEq F]
      (r : ℕ) (hr : 0 < r) (active : Finset Target) (hActive : active.Nonempty)
      (A : Matrix (Target × E) (Fin r) ℂ)
      (B : Matrix (Target × F) (Fin r) ℂ)
      (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
      (hPure :
        let phi : Target × Target → ℂ := fun ab =>
          if ab.1 = ab.2 ∧ ab.1 ∈ active then
            (Real.sqrt ((active.card : ℝ)⁻¹) : ℂ) else 0
        let U : Matrix (Target × Target) (E × F) ℂ :=
          fun ab ef => (A * Bᵀ) (ab.1, ef.1) (ab.2, ef.2)
        U * Uᴴ = (r : ℂ) • vecMulVec phi (star phi)) :
      ∃ m : ℕ, 0 < m ∧ r = active.card * m := by
    classical
    let d := active.card
    have hd : 0 < d := Finset.card_pos.mpr hActive
    let q : ℂ := (Real.sqrt ((d : ℝ)⁻¹) : ℂ)
    let phi : Target × Target → ℂ := fun ab =>
      if ab.1 = ab.2 ∧ ab.1 ∈ active then q else 0
    let W := A * Bᵀ
    let U : Matrix (Target × Target) (E × F) ℂ :=
      fun ab ef => W (ab.1, ef.1) (ab.2, ef.2)
    change U * Uᴴ = (r : ℂ) • vecMulVec phi (star phi) at hPure
    have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    have hq : star q * q = (d : ℂ)⁻¹ := by
      change (starRingEnd ℂ) (Real.sqrt ((d : ℝ)⁻¹) : ℂ) *
        (Real.sqrt ((d : ℝ)⁻¹) : ℂ) = (d : ℂ)⁻¹
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg d)), Complex.ofReal_inv]
      rw [Complex.ofReal_natCast]
    have hphi : dotProduct (star phi) phi = 1 := by
      have hsum : dotProduct (star phi) phi = (d : ℂ) * (star q * q) := by
        unfold dotProduct
        rw [Fintype.sum_prod_type]
        have hterm (a b : Target) : star (phi (a, b)) * phi (a, b) =
            if a = b ∧ a ∈ active then star q * q else 0 := by
          by_cases h : a = b ∧ a ∈ active
          · simp only [phi, if_pos h]
          · simp only [phi, if_neg h, star_zero, mul_zero]
        change (∑ a : Target, ∑ b : Target, star (phi (a, b)) * phi (a, b)) = _
        simp_rw [hterm]
        simp [ite_and, d]
      rw [hsum, hq, mul_inv_cancel₀ hdne]
    let R : Matrix (Target × Target) (Target × Target) ℂ :=
      vecMulVec phi (star phi)
    have hR : R * R = R := by
      simp [R, Matrix.vecMulVec_mul_vecMulVec, hphi]
    have hRU : (1 - R) * U = 0 := by
      apply Matrix.self_mul_conjTranspose_eq_zero.mp
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᴴ, hPure]
      have hstar : (1 - R)ᴴ = 1 - R := by
        simp [R, Matrix.conjTranspose_vecMulVec]
      change (1 - R) * (((r : ℂ) • R) * (1 - R)ᴴ) = 0
      rw [hstar, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_sub, Matrix.mul_one, hR, sub_self, Matrix.mul_zero, smul_zero]
    have hFactor : U = R * U := by
      rw [Matrix.sub_mul, Matrix.one_mul] at hRU
      exact sub_eq_zero.mp hRU
    let envAmp : E × F → ℂ := star phi ᵥ* U
    have hEnv : U = vecMulVec phi envAmp := by
      rw [hFactor]
      exact Matrix.vecMulVec_mul phi (star phi) U
    let env : Matrix E F ℂ := fun e f => q * envAmp (e, f)
    have hfactor (a b : Target) (e : E) (f : F) :
        W (a, e) (b, f) = if a = b ∧ a ∈ active then env e f else 0 := by
      have hentry := congrFun (congrFun hEnv (a, b)) (e, f)
      simpa [U, Matrix.vecMulVec_apply, phi, env] using hentry
    let T := W * Wᴴ
    let G := env * envᴴ
    have hBT : Bᵀ * (Bᵀ)ᴴ = 1 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_one,
        Matrix.conjTranspose_transpose_eq_transpose_conjTranspose] using
        congrArg Matrix.transpose hB
    have hT : T = A * Aᴴ := by
      dsimp [T, W]
      rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
        Matrix.mul_assoc A Bᵀ (Bᵀ)ᴴ, hBT, Matrix.mul_one]
    have hTproj : T * T = T := by
      rw [hT, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ A Aᴴ,
        hA, Matrix.one_mul]
    have hTraceT : T.trace = (r : ℂ) := by
      rw [hT, Matrix.trace_mul_comm, hA]
      simp
    have hBlock (a b : Target) (e f : E) :
        T (a, e) (b, f) = if a = b ∧ a ∈ active then G e f else 0 := by
      dsimp only [T]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
      simp_rw [hfactor]
      rw [Finset.sum_eq_single a]
      · by_cases hab : a = b
        · subst b
          by_cases ha : a ∈ active <;>
            simp [G, Matrix.mul_apply, Matrix.conjTranspose_apply, ha]
        · simp [hab, Ne.symm hab]
      · intro x _ hx
        simp [Ne.symm hx]
      · intro h
        exact False.elim (h (Finset.mem_univ a))
    have hGproj : G * G = G := by
      obtain ⟨a, ha⟩ := hActive
      ext e f
      have hentry := congrFun (congrFun hTproj (a, e)) (a, f)
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, hBlock] at hentry
      rw [Finset.sum_eq_single a] at hentry
      · simpa [ha, Matrix.mul_apply] using hentry
      · intro x _ hx
        simp [Ne.symm hx]
      · intro h
        exact False.elim (h (Finset.mem_univ a))
    have hTrace : T.trace = (d : ℂ) * G.trace := by
      simp only [Matrix.trace, Matrix.diag_apply, hBlock, eq_self_iff_true, true_and]
      rw [Fintype.sum_prod_type]
      simp [Finset.sum_ite_irrel, Finset.sum_ite, d]
    have hId : IsIdempotentElem G.toLin' := by
      change G.toLin'.comp G.toLin' = G.toLin'
      rw [← Matrix.toLin'_mul, hGproj]
    let m := Module.finrank ℂ (LinearMap.range G.toLin')
    have hRank : G.trace = (m : ℂ) := by
      exact (Matrix.trace_toLin'_eq G).symm.trans
        (LinearMap.IsIdempotentElem.isProj_range G.toLin' hId).trace
    have hdim : r = d * m := by
      have hcast : (r : ℂ) = (d : ℂ) * (m : ℂ) := by
        rw [← hTraceT, hTrace, hRank]
      exact_mod_cast hcast
    refine ⟨m, ?_, hdim⟩
    by_contra h
    have hz : m = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hdim
    omega


  have hFlatSectorCard {Sector : Type u} [Fintype Sector] [DecidableEq Sector]
      (d : Sector → ℕ) (s : Sector) :
      (Finset.univ.filter (fun p : Sigma (fun t => Fin (d t)) => p.1 = s)).card = d s := by
    classical
    let e : Fin (d s) ↪ Sigma (fun t => Fin (d t)) :=
      { toFun := fun i => ⟨s, i⟩
        inj' := by intro i j h; exact @sigma_mk_injective Sector (fun t => Fin (d t)) s i j h }
    have hset : Finset.univ.filter (fun p : Sigma (fun t => Fin (d t)) => p.1 = s) =
        Finset.univ.map e := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hp
        rcases p with ⟨t, j⟩
        dsimp at hp
        subst t
        exact ⟨j, rfl⟩
      · rintro ⟨i, hi⟩
        rw [← hi]
        rfl
    rw [hset, Finset.card_map]
    exact Fintype.card_fin (d s)


  have hFlatRestrict {Sector E Target : Type u} [Fintype Sector] [DecidableEq Sector]
      [Fintype E] [DecidableEq E] [Fintype Target] [DecidableEq Target]
      (r : Sector → ℕ) (s : Sector)
      (V : Matrix (E × Target) (Sigma (fun t => Fin (r t))) ℂ)
      (hV : Vᴴ * V = 1) :
      let A : Matrix (Target × E) (Fin (r s)) ℂ := fun p i => V (p.2, p.1) ⟨s, i⟩
      Aᴴ * A = 1 := by
    classical
    intro A
    ext i j
    change (∑ p : Target × E, star (V (p.2, p.1) ⟨s, i⟩) * V (p.2, p.1) ⟨s, j⟩) = _
    rw [Fintype.sum_prod_type]
    have hentry := congrFun (congrFun hV ⟨s, i⟩) ⟨s, j⟩
    change (∑ p : E × Target, star (V p ⟨s, i⟩) * V p ⟨s, j⟩) = _ at hentry
    rw [Fintype.sum_prod_type, Finset.sum_comm] at hentry
    simpa [A, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.one_apply] using hentry


  have hFlatSourceAmplitude {Sector E F Target : Type u} [Fintype Sector] [DecidableEq Sector]
      [Fintype E] [Fintype F] [Fintype Target]
      (r : Sector → ℕ) (s : Sector) (q : ℂ)
      (VX : Matrix (E × Target) (Sigma (fun t => Fin (r t))) ℂ)
      (VY : Matrix (F × Target) (Sigma (fun t => Fin (r t))) ℂ)
      (ex : E) (ey : F) (a b : Target) :
      (∑ i : Sigma (fun t => Fin (r t)), ∑ j : Sigma (fun t => Fin (r t)),
        VX (ex, a) i * (if i = j ∧ i.1 = s then q else 0) * VY (ey, b) j) =
      q * ∑ i : Fin (r s), VX (ex, a) ⟨s, i⟩ * VY (ey, b) ⟨s, i⟩ := by
    classical
    simp [ite_and, Fintype.sum_sigma, Finset.mul_sum]
    rw [Finset.sum_eq_single s]
    · simp only [if_true]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · intro t _ ht
      simp [ht]
    · intro h
      exact False.elim (h (Finset.mem_univ s))


  have hFlatUnnormalize {P E : Type u} [Fintype P] [DecidableEq P] [Fintype E]
      (r : ℕ) (hr : 0 < r) (U : Matrix P E ℂ) (phi : P → ℂ)
      (hout :
        let q : ℂ := (Real.sqrt ((r : ℝ)⁻¹) : ℂ)
        ∀ a b, ∑ e, (q * U a e) * star (q * U b e) = phi a * star (phi b)) :
      U * Uᴴ = (r : ℂ) • vecMulVec phi (star phi) := by
    classical
    let q : ℂ := (Real.sqrt ((r : ℝ)⁻¹) : ℂ)
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
    have hq : q * star q = (r : ℂ)⁻¹ := by
      change (Real.sqrt ((r : ℝ)⁻¹) : ℂ) *
        (starRingEnd ℂ) (Real.sqrt ((r : ℝ)⁻¹) : ℂ) = (r : ℂ)⁻¹
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg r)),
        Complex.ofReal_inv, Complex.ofReal_natCast]
    ext a b
    have h := hout a b
    change (∑ e, (q * U a e) * star (q * U b e)) = _ at h
    have hnorm : (q * star q) * (U * Uᴴ) a b = phi a * star (phi b) := by
      calc
        (q * star q) * (U * Uᴴ) a b = ∑ e, (q * U a e) * star (q * U b e) := by
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, star_mul]
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = _ := h
    rw [hq] at hnorm
    have hscaled := congrArg (fun z : ℂ => (r : ℂ) * z) hnorm
    simpa [mul_assoc, hrne, Matrix.vecMulVec_apply] using hscaled



  have hFlatNecessary (r d : Sector → ℕ)
      (hr : ∀ s, 0 < r s) (hd : ∀ s, 0 < d s)
      (left right : QuantumChannel (TargetLocal r) (TargetLocal d))
      (hBasis : ∀ s, tensorRawAction left right
        (Matrix.vecMulVec (fun xy => targetEncoding r xy s) (star (fun xy => targetEncoding r xy s))) =
        Matrix.vecMulVec (fun xy => targetEncoding d xy s) (star (fun xy => targetEncoding d xy s))) :
      ∀ s, ∃ m : ℕ, 0 < m ∧ r s = d s * m := by
    obtain ⟨VX, hVX, hLX⟩ := (channel_kraus_stinespring).2 left
    obtain ⟨VY, hVY, hLY⟩ := (channel_kraus_stinespring).2 right
    intro s
    let active : Finset (TargetLocal d) := Finset.univ.filter (fun p => p.1 = s)
    have hCard : active.card = d s := hFlatSectorCard d s
    have hActive : active.Nonempty := Finset.card_pos.mp (by rw [hCard]; exact hd s)
    let A : Matrix (TargetLocal d × (TargetLocal d × TargetLocal r)) (Fin (r s)) ℂ :=
      fun p i => VX (p.2, p.1) ⟨s, i⟩
    let B : Matrix (TargetLocal d × (TargetLocal d × TargetLocal r)) (Fin (r s)) ℂ :=
      fun p i => VY (p.2, p.1) ⟨s, i⟩
    have hA : Aᴴ * A = 1 := hFlatRestrict r s VX hVX
    have hB : Bᴴ * B = 1 := hFlatRestrict r s VY hVY
    let q : ℂ := (Real.sqrt ((r s : ℝ)⁻¹) : ℂ)
    let U : Matrix (TargetLocal d × TargetLocal d)
        ((TargetLocal d × TargetLocal r) × (TargetLocal d × TargetLocal r)) ℂ :=
      fun ab ef => (A * Bᵀ) (ab.1, ef.1) (ab.2, ef.2)
    have hSourceEntry (i j : TargetLocal r) :
        targetEncoding r (i, j) s = if i = j ∧ i.1 = s then q else 0 := by
      dsimp only [targetEncoding]
      by_cases h : i = j ∧ i.1 = s
      · rw [if_pos h, if_pos h, h.2]
      · rw [if_neg h, if_neg h]
    have hXi (ex ey : TargetLocal d × TargetLocal r) (ab : TargetLocal d × TargetLocal d) :
        (∑ i : TargetLocal r, ∑ j : TargetLocal r,
          VX (ex, ab.1) i * targetEncoding r (i, j) s * VY (ey, ab.2) j) =
        q * U ab (ex, ey) := by
      simp_rw [hSourceEntry]
      exact hFlatSourceAmplitude r s q VX VY ex ey ab.1 ab.2
    let Xi : Sector → Matrix
        ((TargetLocal d × TargetLocal r) × (TargetLocal d × TargetLocal r))
        (TargetLocal d × TargetLocal d) ℂ := fun t e o =>
      ∑ i : TargetLocal r, ∑ j : TargetLocal r,
        VX (e.1, o.1) i * targetEncoding r (i, j) t * VY (e.2, o.2) j
    have hDil (t v : Sector) (o u : TargetLocal d × TargetLocal d) :
        tensorRawAction left right
          (Matrix.vecMulVec (fun i => targetEncoding r i t)
            (star (fun i => targetEncoding r i v))) o u =
          ∑ e, Xi t e o * star (Xi v e u) := by
      have hLeft (i j : TargetLocal r) (a b : TargetLocal d) :
          CStarMatrix.ofMatrix.symm
            (left.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) a b =
            ∑ ex : TargetLocal d × TargetLocal r, VX (ex, a) i * star (VX (ex, b) j) := by
        rw [← hLX]
        simp [partialTraceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.single, ite_and]
      have hRight (i j : TargetLocal r) (a b : TargetLocal d) :
          CStarMatrix.ofMatrix.symm
            (right.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) a b =
            ∑ ey : TargetLocal d × TargetLocal r, VY (ey, a) i * star (VY (ey, b) j) := by
        rw [← hLY]
        simp [partialTraceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.single, ite_and]
      rw [Fintype.sum_prod_type]
      simp only [tensorRawAction, Matrix.vecMulVec_apply, Pi.star_apply, hLeft, hRight,
        Xi, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
      conv_rhs =>
        arg 2
        ext ex
        rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext i
        arg 2
        ext ex
        arg 2
        ext ey
        rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext i
        arg 2
        ext ex
        rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext i
        arg 2
        ext j
        arg 2
        ext ex
        rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext i
        arg 2
        ext j
        rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext i
        arg 2
        ext j
        arg 2
        ext a
        arg 2
        ext ex
        rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext i
        arg 2
        ext j
        arg 2
        ext a
        rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext i
        arg 2
        ext j
        rw [Finset.sum_comm]
      conv_lhs =>
        arg 2
        ext i
        arg 2
        ext j
        arg 2
        ext a
        arg 2
        ext b
        rw [Finset.sum_comm]
      repeat' (apply Finset.sum_congr rfl; intro x hx)
      ring
    have hNorm (a b : TargetLocal d × TargetLocal d) :
        (∑ ef, (q * U a ef) * star (q * U b ef)) =
        targetEncoding d a s * star (targetEncoding d b s) := by
      have h := hDil s s a b
      dsimp only [Xi] at h
      rw [hBasis s] at h
      simp only [Matrix.vecMulVec_apply, Pi.star_apply] at h
      simp_rw [hXi] at h
      simpa only [Fintype.sum_prod_type] using h.symm
    have hPure : U * Uᴴ = (r s : ℂ) •
        Matrix.vecMulVec (fun xy => targetEncoding d xy s) (star (fun xy => targetEncoding d xy s)) :=
      hFlatUnnormalize (r s) (hr s) U (fun xy => targetEncoding d xy s) hNorm
    have hTargetEntry (ab : TargetLocal d × TargetLocal d) :
        targetEncoding d ab s =
        (if ab.1 = ab.2 ∧ ab.1 ∈ active then
          (Real.sqrt ((active.card : ℝ)⁻¹) : ℂ) else 0) := by
      dsimp only [targetEncoding]
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hCard]
      by_cases h : ab.1 = ab.2 ∧ ab.1.1 = s
      · rw [if_pos h, if_pos h, h.2]
      · rw [if_neg h, if_neg h]
    have hPhi : (fun xy => targetEncoding d xy s) =
        (fun ab => if ab.1 = ab.2 ∧ ab.1 ∈ active then
          (Real.sqrt ((active.card : ℝ)⁻¹) : ℂ) else 0) := funext hTargetEntry
    rw [hPhi] at hPure
    obtain ⟨m, hm, hdim⟩ := hFlatNecessity (r s) (hr s) active hActive A B hA hB hPure
    exact ⟨m, hm, by simpa only [hCard] using hdim⟩



  have hGlobalFlatIsometry {Sector : Type u} [Fintype Sector] [DecidableEq Sector]
      (r d m : Sector → ℕ) (hdim : ∀ s, r s = d s * m s) :
      ∃ V : Matrix
        (Sigma (fun s => Fin (d s)) × Sigma (fun s => Fin (m s)))
        (Sigma (fun s => Fin (r s))) ℂ,
        Vᴴ * V = 1 ∧
        ∀ (s : Sector) (a b : Sigma (fun t => Fin (d t)))
          (ex ey : Sigma (fun t => Fin (m t))),
          (∑ i : Fin (r s), V (a, ex) ⟨s, i⟩ * V (b, ey) ⟨s, i⟩) =
            (if a = b ∧ a.1 = s then 1 else 0) *
            (if ex = ey ∧ ex.1 = s then 1 else 0) := by
    classical
    let e (s : Sector) : Fin (r s) ≃ Fin (d s) × Fin (m s) :=
      (finCongr (hdim s)).trans finProdFinEquiv.symm
    let f : Sigma (fun s => Fin (r s)) →
        Sigma (fun s => Fin (d s)) × Sigma (fun s => Fin (m s)) :=
      fun p => (⟨p.1, (e p.1 p.2).1⟩, ⟨p.1, (e p.1 p.2).2⟩)
    have hf : Function.Injective f := by
      rintro ⟨s, i⟩ ⟨t, j⟩ h
      have hs : s = t := congrArg (fun p => p.1.1) h
      subst t
      have ha : (e s i).1 = (e s j).1 :=
        @sigma_mk_injective Sector (fun t => Fin (d t)) s _ _ (congrArg Prod.fst h)
      have hb : (e s i).2 = (e s j).2 :=
        @sigma_mk_injective Sector (fun t => Fin (m t)) s _ _ (congrArg Prod.snd h)
      have hij := (e s).injective (Prod.ext ha hb)
      subst j
      rfl
    let V : Matrix
        (Sigma (fun s => Fin (d s)) × Sigma (fun s => Fin (m s)))
        (Sigma (fun s => Fin (r s))) ℂ :=
      fun p i => if f i = p then 1 else 0
    have hV : Vᴴ * V = 1 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_eq_single (f i)]
      · simp [V, hf.eq_iff, Matrix.one_apply, eq_comm]
      · intro p _ hp
        simp [V, Ne.symm hp]
      · intro h
        exact False.elim (h (Finset.mem_univ (f i)))
    refine ⟨V, hV, ?_⟩
    rintro s ⟨ta, a⟩ ⟨tb, b⟩ ⟨te, ex⟩ ⟨tf, ey⟩
    by_cases ha : ta = s
    · subst ta
      by_cases hb : tb = s
      · subst tb
        by_cases he : te = s
        · subst te
          by_cases hff : tf = s
          · subst tf
            rw [Finset.sum_eq_single ((e s).symm (a, ex))]
            · by_cases hab : a = b <;> by_cases hee : ex = ey <;>
                simp [V, f, eq_comm, hab, hee]
            · intro i _ hi
              have hnot : e s i ≠ (a, ex) := by
                intro h
                apply hi
                exact (e s).injective (h.trans ((e s).apply_symm_apply (a, ex)).symm)
              have hn : f ⟨s, i⟩ ≠ (⟨s, a⟩, ⟨s, ex⟩) := by
                intro h
                apply hnot
                exact Prod.ext
                  (@sigma_mk_injective Sector (fun t => Fin (d t)) s _ _ (congrArg Prod.fst h))
                  (@sigma_mk_injective Sector (fun t => Fin (m t)) s _ _ (congrArg Prod.snd h))
              simp [V, hn]
            · intro h
              exact False.elim (h (Finset.mem_univ ((e s).symm (a, ex))))
          · simp [V, f, hff, Ne.symm hff, eq_comm]
        · simp [V, f, he, Ne.symm he, eq_comm]
      · simp [V, f, hb, Ne.symm hb, eq_comm]
    · simp [V, f, ha, Ne.symm ha, eq_comm]


  have hFlatIsometryChannel {Source Target E : Type u} [Fintype Source] [DecidableEq Source]
      [Fintype Target] [DecidableEq Target] [Fintype E] [DecidableEq E]
      (V : Matrix (Target × E) Source ℂ) (hV : Vᴴ * V = 1) :
      ∃ C : QuantumChannel Source Target,
        ∀ (rho : Matrix Source Source ℂ) (a b : Target),
          CStarMatrix.ofMatrix.symm
            (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) a b =
          ∑ e : E, (V * rho * Vᴴ) (a, e) (b, e) := by
    classical
    let K : E → Matrix Target Source ℂ := fun e a i => V (a, e) i
    have hK : (∑ e, (K e)ᴴ * K e) = 1 := by
      ext i j
      have hentry := congrFun (congrFun hV i) j
      change (∑ p : Target × E, star (V p i) * V p j) = _ at hentry
      rw [Fintype.sum_prod_type, Finset.sum_comm] at hentry
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      change (∑ e : E, ∑ a : Target, star (V (a, e) i) * V (a, e) j) = _
      exact hentry
    obtain ⟨C, hC⟩ :=
      D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel K hK
    refine ⟨C, ?_⟩
    intro rho a b
    rw [hC]
    simp only [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro e _
    rfl


  have hTensorFromSlices {ax ay bx oy EX EY Sector : Type u}
      [Fintype ax] [DecidableEq ax] [Fintype ay] [DecidableEq ay]
      [Fintype bx] [DecidableEq bx] [Fintype oy] [DecidableEq oy]
      [Fintype EX] [Fintype EY] [Fintype Sector] [DecidableEq Sector]
      (left : QuantumChannel ax bx) (right : QuantumChannel ay oy)
      (VX : Matrix (bx × EX) ax ℂ) (VY : Matrix (oy × EY) ay ℂ)
      (hLeft : ∀ i j o u,
        CStarMatrix.ofMatrix.symm
          (left.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) o u =
        ∑ ex : EX, VX (o, ex) i * star (VX (u, ex) j))
      (hRight : ∀ i j o u,
        CStarMatrix.ofMatrix.symm
          (right.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) o u =
        ∑ ey : EY, VY (o, ey) i * star (VY (u, ey) j))
      (H : Matrix (ax × ay) Sector ℂ) :
      ∀ (s t : Sector) (o u : bx × oy),
        let Xi : Sector → EX → EY → bx × oy → ℂ :=
          fun s ex ey o => ∑ i : ax, ∑ j : ay,
            VX (o.1, ex) i * H (i, j) s * VY (o.2, ey) j
        tensorRawAction left right
          (Matrix.vecMulVec (fun i => H i s) (star (fun i => H i t))) o u =
        ∑ ex, ∑ ey, Xi s ex ey o * star (Xi t ex ey u) := by
    intro s t o u Xi
    simp only [tensorRawAction, Matrix.vecMulVec_apply, Pi.star_apply, hLeft, hRight,
      Xi, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    conv_rhs =>
      arg 2
      ext ex
      rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs =>
      arg 2
      ext i
      arg 2
      ext ex
      arg 2
      ext ey
      rw [Finset.sum_comm]
    conv_rhs =>
      arg 2
      ext i
      arg 2
      ext ex
      rw [Finset.sum_comm]
    conv_rhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    conv_rhs =>
      arg 2
      ext i
      arg 2
      ext j
      arg 2
      ext ex
      rw [Finset.sum_comm]
    conv_rhs =>
      arg 2
      ext i
      arg 2
      ext j
      rw [Finset.sum_comm]
    conv_rhs =>
      arg 2
      ext i
      arg 2
      ext j
      arg 2
      ext a
      arg 2
      ext ex
      rw [Finset.sum_comm]
    conv_rhs =>
      arg 2
      ext i
      arg 2
      ext j
      arg 2
      ext a
      rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs =>
      arg 2
      ext i
      arg 2
      ext j
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext i
      arg 2
      ext j
      arg 2
      ext a
      arg 2
      ext b
      rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro x hx)
    ring


  have hFlatSufficient (r d m : Sector → ℕ)
      (hr : ∀ s, 0 < r s) (hd : ∀ s, 0 < d s) (hm : ∀ s, 0 < m s)
      (hdim : ∀ s, r s = d s * m s) :
      ∃ left : QuantumChannel (TargetLocal r) (TargetLocal d),
      ∃ right : QuantumChannel (TargetLocal r) (TargetLocal d),
      ∀ s, tensorRawAction left right
        (Matrix.vecMulVec (fun xy => targetEncoding r xy s) (star (fun xy => targetEncoding r xy s))) =
        Matrix.vecMulVec (fun xy => targetEncoding d xy s) (star (fun xy => targetEncoding d xy s)) := by
    obtain ⟨V, hV, hFactor⟩ := hGlobalFlatIsometry r d m hdim
    obtain ⟨C, hC⟩ := hFlatIsometryChannel V hV
    have hSlice (i j : TargetLocal r) (a b : TargetLocal d) :
        CStarMatrix.ofMatrix.symm
          (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) a b =
        ∑ e : TargetLocal m, V (a, e) i * star (V (b, e) j) := by
      rw [hC]
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single, ite_and]
    have hTensor := hTensorFromSlices C C V V hSlice hSlice (targetEncoding r)
    refine ⟨C, C, ?_⟩
    intro s
    let qR : ℂ := (Real.sqrt ((r s : ℝ)⁻¹) : ℂ)
    let qD : ℂ := (Real.sqrt ((d s : ℝ)⁻¹) : ℂ)
    let g : TargetLocal m × TargetLocal m → ℂ := fun ef =>
      if ef.1 = ef.2 ∧ ef.1.1 = s then 1 else 0
    let phi : TargetLocal d × TargetLocal d → ℂ := fun ab =>
      if ab.1 = ab.2 ∧ ab.1.1 = s then qD else 0
    let U : Matrix (TargetLocal d × TargetLocal d) (TargetLocal m × TargetLocal m) ℂ :=
      fun ab ef => ∑ i : Fin (r s), V (ab.1, ef.1) ⟨s, i⟩ * V (ab.2, ef.2) ⟨s, i⟩
    have hU (ab : TargetLocal d × TargetLocal d) (ef : TargetLocal m × TargetLocal m) :
        U ab ef = (if ab.1 = ab.2 ∧ ab.1.1 = s then 1 else 0) * g ef :=
      hFactor s ab.1 ab.2 ef.1 ef.2
    have hEnv : (∑ ef, g ef * star (g ef)) = (m s : ℂ) := by
      have hterm (ef : TargetLocal m × TargetLocal m) : g ef * star (g ef) = g ef := by
        by_cases h : ef.1 = ef.2 ∧ ef.1.1 = s
        · simp only [g, if_pos h, star_one, mul_one]
        · simp only [g, if_neg h, star_zero, mul_zero]
      simp_rw [hterm]
      simp [g, Fintype.sum_prod_type, ite_and, Finset.sum_boole, hFlatSectorCard m s]
    have hq (n : ℕ) : (Real.sqrt ((n : ℝ)⁻¹) : ℂ) *
        star (Real.sqrt ((n : ℝ)⁻¹) : ℂ) = (n : ℂ)⁻¹ := by
      change (Real.sqrt ((n : ℝ)⁻¹) : ℂ) *
        (starRingEnd ℂ) (Real.sqrt ((n : ℝ)⁻¹) : ℂ) = _
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg n)),
        Complex.ofReal_inv, Complex.ofReal_natCast]
    have hqR : qR * star qR = (r s : ℂ)⁻¹ := hq (r s)
    have hqD : qD * star qD = (d s : ℂ)⁻¹ := hq (d s)
    have hCoeff : (r s : ℂ)⁻¹ * (m s : ℂ) = (d s : ℂ)⁻¹ := by
      have hDne : (d s : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hd s)
      have hMne : (m s : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hm s)
      have hR : (r s : ℂ) = (d s : ℂ) * (m s : ℂ) := by exact_mod_cast hdim s
      rw [hR]
      field_simp
    have hNorm (a b : TargetLocal d × TargetLocal d) :
        (∑ ef, (qR * U a ef) * star (qR * U b ef)) = phi a * star (phi b) := by
      by_cases ha : a.1 = a.2 ∧ a.1.1 = s
      · by_cases hb : b.1 = b.2 ∧ b.1.1 = s
        · simp only [hU, phi, if_pos ha, if_pos hb, one_mul]
          calc
            (∑ ef, (qR * g ef) * star (qR * g ef)) =
                (qR * star qR) * ∑ ef, g ef * star (g ef) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ef _
              rw [star_mul]
              ring
            _ = qD * star qD := by rw [hEnv, hqR, hqD, hCoeff]
        · simp only [hU, phi, if_pos ha, if_neg hb, one_mul, zero_mul, mul_zero,
            star_zero, Finset.sum_const_zero]
      · simp only [hU, phi, if_neg ha, zero_mul, mul_zero, Finset.sum_const_zero]
    have hSourceEntry (i j : TargetLocal r) :
        targetEncoding r (i, j) s = if i = j ∧ i.1 = s then qR else 0 := by
      dsimp only [targetEncoding]
      by_cases h : i = j ∧ i.1 = s
      · rw [if_pos h, if_pos h, h.2]
      · rw [if_neg h, if_neg h]
    have hXi (ex ey : TargetLocal m) (ab : TargetLocal d × TargetLocal d) :
        (∑ i : TargetLocal r, ∑ j : TargetLocal r,
          V (ab.1, ex) i * targetEncoding r (i, j) s * V (ab.2, ey) j) =
        qR * U ab (ex, ey) := by
      simp_rw [hSourceEntry]
      exact hFlatSourceAmplitude r s qR
        (fun p i => V (p.2, p.1) i) (fun p i => V (p.2, p.1) i) ex ey ab.1 ab.2
    have hTargetEntry (ab : TargetLocal d × TargetLocal d) : targetEncoding d ab s = phi ab := by
      dsimp only [targetEncoding, phi]
      by_cases h : ab.1 = ab.2 ∧ ab.1.1 = s
      · rw [if_pos h, if_pos h, h.2]
      · rw [if_neg h, if_neg h]
    ext a b
    have h := hTensor s s a b
    dsimp only at h
    simp_rw [hXi] at h
    have hNormSlices := hNorm a b
    rw [Fintype.sum_prod_type] at hNormSlices
    rw [hNormSlices] at h
    simpa only [Matrix.vecMulVec_apply, Pi.star_apply, hTargetEntry] using h

  have hFlatFeasibility : FlatFeasibilityClaim (Sector := Sector) := by
    intro r d hr hd
    constructor
    · rintro ⟨left, right, hBasis⟩
      exact hFlatNecessary r d hr hd left right hBasis
    · intro hMultipliers
      let m : Sector → ℕ := fun s => (hMultipliers s).choose
      have hm : ∀ s, 0 < m s := fun s => (hMultipliers s).choose_spec.1
      have hdim : ∀ s, r s = d s * m s := fun s => (hMultipliers s).choose_spec.2
      exact hFlatSufficient r d m hr hd hm hdim

  exact hFlatFeasibility

end D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
