/- GID: D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/SicMubCorrelationTraceNormEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: SIC and complete-MUB correlation trace norms differ by the dimension factor. -/

import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB
import D5.S3.Quantum.Tomography.CompleteContextTomography

/-!
SIC and complete-MUB correlation matrices have proportional trace norms, with the product of the
local factors `sqrt (d * (d + 1))`.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality

open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB (MUBFamily)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)

def SICFamily (d : ℕ) :=
  {ψ : Fin (d * d) → Fin d → ℂ //
    (∀ i, star (ψ i) ⬝ᵥ ψ i = 1) ∧
    ∀ i j, i ≠ j → ‖star (ψ i) ⬝ᵥ ψ j‖ ^ 2 = 1 / ((d : ℝ) + 1)}

def sicEffect {d : ℕ} (S : SICFamily d) (i : Fin (d * d)) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((d : ℂ)⁻¹) • vecMulVec (S.1 i) (star (S.1 i))

def sicCorrelation {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (SA : SICFamily dA) (SB : SICFamily dB) :
    Matrix (Fin (dA * dA)) (Fin (dB * dB)) ℂ :=
  of fun i j => (ρ * (sicEffect SA i ⊗ₖ sicEffect SB j)).trace

def mubCorrelation {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (MA : MUBFamily dA (dA + 1)) (MB : MUBFamily dB (dB + 1)) :
    Matrix (Fin (dA + 1) × Fin dA) (Fin (dB + 1) × Fin dB) ℂ :=
  of fun p q => (ρ * (MA.effect p ⊗ₖ MB.effect q)).trace

def claim : Prop :=
  ∀ (dA dB : ℕ), 2 ≤ dA → 2 ≤ dB →
    ∀ (SA : SICFamily dA) (SB : SICFamily dB)
      (MA : MUBFamily dA (dA + 1)) (MB : MUBFamily dB (dB + 1))
      (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      ρ.PosSemidef → ρ.trace = 1 →
        traceNorm (mubCorrelation ρ MA MB) =
          Real.sqrt (dA * (dA + 1)) * Real.sqrt (dB * (dB + 1)) *
            traceNorm (sicCorrelation ρ SA SB)

private def sicProjector {d : ℕ} (S : SICFamily d) (i : Fin (d * d)) :
    Matrix (Fin d) (Fin d) ℂ := vecMulVec (S.1 i) (star (S.1 i))

private theorem sicProjector_trace {d : ℕ} (S : SICFamily d) (i : Fin (d * d)) :
    (sicProjector S i).trace = 1 := by
  rw [sicProjector, trace_vecMulVec, dotProduct_comm]
  exact S.2.1 i

private theorem sicProjector_gram {d : ℕ} (S : SICFamily d) (i j : Fin (d * d)) :
    (sicProjector S i * sicProjector S j).trace =
      (d : ℂ) / (d + 1) * (if i = j then 1 else 0) + 1 / (d + 1) := by
  have h := D5.S3.Observer.BornReduction.rank_one_pure_state_modulus_square_reduction
    (fun k => sicProjector S k) (sicProjector S j) i (S.1 i) (S.1 j) rfl rfl
  change (sicProjector S j * sicProjector S i).trace = _ at h
  rw [Matrix.trace_mul_comm] at h
  rw [h]
  by_cases hij : i = j
  · subst j
    rw [S.2.1 i]
    simp only [norm_one, one_pow, Complex.ofReal_one]
    have hd : (d : ℂ) + 1 ≠ 0 := by positivity
    field_simp
    simp only [ite_true, mul_one]
  · rw [S.2.2 i j hij]
    simp only [hij, ite_false, mul_zero, zero_add, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast]

private theorem sicProjector_span {d : ℕ} (hd : 2 ≤ d) (S : SICFamily d) :
    Submodule.span ℂ (Set.range (sicProjector S)) = ⊤ := by
  classical
  let K : LinearMap.BilinForm ℂ (Matrix (Fin d) (Fin d) ℂ) :=
    LinearMap.compr₂ (LinearMap.mul ℂ (Matrix (Fin d) (Fin d) ℂ))
      (Matrix.traceLinearMap (Fin d) ℂ ℂ)
  let τ := Matrix.traceLinearMap (Fin d) ℂ ℂ
  let B : LinearMap.BilinForm ℂ (Matrix (Fin d) (Fin d) ℂ) :=
    K - (1 / (d + 1) : ℂ) • τ.smulRight τ
  have hlin : LinearIndependent ℂ (sicProjector S) := by
    apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := B)
    · intro i j hij
      change (sicProjector S i * sicProjector S j).trace -
        1 / (d + 1) * ((sicProjector S i).trace * (sicProjector S j).trace) = 0
      rw [sicProjector_gram, sicProjector_trace, sicProjector_trace]
      simp only [hij, ite_false, mul_zero, zero_add, mul_one, sub_self]
    · intro i
      change (sicProjector S i * sicProjector S i).trace -
        1 / (d + 1) * ((sicProjector S i).trace * (sicProjector S i).trace) ≠ 0
      rw [sicProjector_gram, sicProjector_trace]
      simp only [ite_true, mul_one, add_sub_cancel_right]
      exact div_ne_zero (by exact_mod_cast (by omega : d ≠ 0)) (by positivity)
  apply hlin.span_eq_top_of_card_eq_finrank'
  simp only [Fintype.card_fin, Module.finrank_matrix, Module.finrank_self, mul_one]

private theorem trace_pairing_ext {d : ℕ} {ι : Type*}
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hP : Submodule.span ℂ (Set.range P) = ⊤)
    {X Y : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ i, (X * P i).trace = (Y * P i).trace) : X = Y := by
  let K : LinearMap.BilinForm ℂ (Matrix (Fin d) (Fin d) ℂ) :=
    LinearMap.compr₂ (LinearMap.mul ℂ (Matrix (Fin d) (Fin d) ℂ))
      (Matrix.traceLinearMap (Fin d) ℂ ℂ)
  have heq : K X = K Y := LinearMap.ext_on_range hP h
  exact Matrix.ext_iff_trace_mul_right.mpr (fun Z => LinearMap.congr_fun heq Z)

private theorem sicProjector_sum {d : ℕ} (hd : 2 ≤ d) (S : SICFamily d) :
    ∑ i, sicProjector S i = (d : ℂ) • 1 := by
  classical
  apply trace_pairing_ext (sicProjector S) (sicProjector_span hd S)
  intro j
  let K : LinearMap.BilinForm ℂ (Matrix (Fin d) (Fin d) ℂ) :=
    LinearMap.compr₂ (LinearMap.mul ℂ (Matrix (Fin d) (Fin d) ℂ))
      (Matrix.traceLinearMap (Fin d) ℂ ℂ)
  have hgram (i k : Fin (d * d)) :
      K (sicProjector S i) (sicProjector S k) =
        if i = k then (1 : ℂ) ^ 2 else 1 / (d + 1) := by
    change (sicProjector S i * sicProjector S k).trace = _
    rw [sicProjector_gram]
    by_cases h : i = k <;> simp only [h, ite_true, ite_false, one_pow, mul_one,
      mul_zero, zero_add]
    field_simp
  have h := D5.S3.QuadraticForms.GerzonEqualityParameterIdentity.gram_pair_sum
    K (sicProjector S) 1 (1 / (d + 1)) hgram (fun _ => 1) j
  simp only [one_smul, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul] at h
  calc
    _ = (1 - 1 / ((d : ℂ) + 1)) + 1 / (d + 1) * (d * d) := h
    _ = (d : ℂ) := by field_simp; ring
    _ = _ := by
      simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
        sicProjector_trace, smul_eq_mul, mul_one]

private theorem sic_frame {d : ℕ} (hd : 2 ≤ d) (S : SICFamily d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, (sicEffect S i * X).trace •
      (((d : ℂ) + 1) • sicProjector S i - 1) = X := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℂ) + 1 ≠ 0 := by positivity
  let D (i : Fin (d * d)) := ((d : ℂ) + 1) • sicProjector S i - 1
  have hD : ∑ i, D i = (d : ℂ) • 1 := by
    simp only [D, Finset.sum_sub_distrib, ← Finset.smul_sum,
      sicProjector_sum hd S, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_mul, smul_smul]
    module
  have hb (j : Fin (d * d)) :
      ∑ i, (sicEffect S i * sicProjector S j).trace • D i = sicProjector S j := by
    simp only [sicEffect, ← sicProjector.eq_def, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul, sicProjector_gram, mul_add, add_smul, Finset.sum_add_distrib]
    have hδ : ∑ i, ((d : ℂ)⁻¹ * ((d : ℂ) / (d + 1) * (if i = j then 1 else 0))) •
        D i = ((d : ℂ) + 1)⁻¹ • D j := by
      simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      congr 1
      field_simp
    rw [hδ, ← Finset.smul_sum, hD]
    dsimp only [D]
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hd1, one_smul]
    have hcancel : (d : ℂ)⁻¹ * (1 / (d + 1)) * d = ((d : ℂ) + 1)⁻¹ := by
      field_simp
    rw [smul_smul, hcancel]
    abel
  let T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    ∑ i, ((Matrix.traceLinearMap (Fin d) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ (sicEffect S i))).smulRight (D i)
  have hT : T = LinearMap.id := by
    apply LinearMap.ext_on_range (sicProjector_span hd S)
    intro j
    simpa only [T, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, Matrix.traceLinearMap_apply, LinearMap.mulLeft_apply,
      LinearMap.id_apply] using hb j
  simpa only [T, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, Matrix.traceLinearMap_apply, LinearMap.mulLeft_apply,
    LinearMap.id_apply] using LinearMap.congr_fun hT X

private theorem mub_gram {d : ℕ} (M : MUBFamily d (d + 1))
    (p q : Fin (d + 1) × Fin d) :
    (M.effect p * M.effect q).trace =
      if p.1 = q.1 then (if p.2 = q.2 then 1 else 0) else (d : ℂ)⁻¹ := by
  rw [show M.effect p =
    D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj (M.ket p.1 p.2) from rfl,
    show M.effect q =
    D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj (M.ket q.1 q.2) from rfl,
    D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj_overlap]
  change ((‖((M.1 p.1).1ᴴ * (M.1 q.1).1) p.2 q.2‖ ^ 2 : ℝ) : ℂ) = _
  by_cases hpq : p.1 = q.1
  · rw [ite_eq_left hpq, hpq]
    have hu := Unitary.star_mul_self_of_mem (M.1 q.1).2
    change (M.1 q.1).1ᴴ * (M.1 q.1).1 = 1 at hu
    rw [hu]
    by_cases hab : p.2 = q.2 <;> simp only [Matrix.one_apply, hab, ite_true, ite_false,
      norm_one, norm_zero, one_pow, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_one,
      Complex.ofReal_zero]
  · rw [ite_eq_right hpq, M.2 p.1 q.1 hpq p.2 q.2]
    simp only [Complex.ofReal_natCast, one_div, Complex.ofReal_inv]

private theorem mub_frame {d : ℕ} (hd : 2 ≤ d) (M : MUBFamily d (d + 1))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ p, (M.effect p * X).trace • M.effect p = X + X.trace • 1 := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hsum (l : Fin (d + 1)) : ∑ a, M.effect (l, a) = 1 := by
    ext i j
    change (∑ a, D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj
      (M.ket l a)) i j = _
    simp only [Matrix.sum_apply, MState.pure_apply]
    change ∑ a, (M.1 l).1 i a * star ((M.1 l).1 j a) = _
    exact congrArg (fun N : Matrix (Fin d) (Fin d) ℂ => N i j)
      (Unitary.mul_star_self_of_mem (M.1 l).2)
  have htrace (p : Fin (d + 1) × Fin d) : (M.effect p).trace = 1 :=
    MState.tr' (MState.pure (M.ket p.1 p.2))
  have hproj (q : Fin (d + 1) × Fin d) :
      ∑ p, (M.effect p * M.effect q).trace • M.effect p = M.effect q + 1 := by
    simp only [mub_gram, Fintype.sum_prod_type]
    have hl (l : Fin (d + 1)) :
        ∑ a, (if l = q.1 then (if a = q.2 then (1 : ℂ) else 0) else (d : ℂ)⁻¹) •
          M.effect (l, a) =
        if l = q.1 then M.effect q else (d : ℂ)⁻¹ • 1 := by
      by_cases h : l = q.1
      · subst l
        simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
      · simp only [ite_eq_right h, ← Finset.smul_sum, hsum]
    simp_rw (congrConsts := false) [hl]
    have heq (l : Fin (d + 1)) :
        (if l = q.1 then M.effect q else (d : ℂ)⁻¹ • 1) =
        (if l = q.1 then M.effect q - (d : ℂ)⁻¹ • 1 else 0) + (d : ℂ)⁻¹ • 1 := by
      split_ifs <;> abel
    simp_rw (congrConsts := false) [heq]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_add, Nat.cast_one]
    have hcancel : ((d : ℂ) + 1) * (d : ℂ)⁻¹ = 1 + (d : ℂ)⁻¹ := by
      field_simp
    rw [hcancel, add_smul, one_smul]
    abel
  cases d with
  | zero => omega
  | succ n =>
    let context : Fin (n + 2) →
        D5.S3.Quantum.Tomography.RankOneContextCommutator.RankOneContext (n + 1) :=
      fun l => {
        projector := fun a => M.effect (l, a)
        rankOne := fun a => by
          let v := M.ket l a
          have hscaled :
              D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.ScaledPure
                (M.effect (l, a)) := ⟨1, v, zero_le_one, (one_smul ℂ _).symm⟩
          refine ⟨(D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.scaledPure_hermitian
            hscaled).eq, ?_, htrace (l, a), ?_⟩
          · exact (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake
              v.vec (D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.ket_dot_self v)
              1).1
          · intro Y
            rw [D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.scaledPure_sandwich
              hscaled, Matrix.trace_mul_comm]
        resolvesIdentity := hsum l }
    have hoverlap (l k : Fin (n + 2)) (a b : Fin (n + 1)) :
        ((context l).projector a * (context k).projector b).trace =
          if l = k then (if a = b then 1 else 0) else ((n + 1 : ℕ) : ℂ)⁻¹ :=
      mub_gram M (l, a) (k, b)
    apply (D5.S3.Quantum.Tomography.CompleteContextTomography.complete_context_tomography
      context hoverlap).2.2
    intro l a
    change ((∑ p, (M.effect p * X).trace • M.effect p) * M.effect (l, a)).trace =
      ((X + X.trace • 1) * M.effect (l, a)).trace
    have h := congrArg (fun N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
      (X * N).trace) (hproj (l, a))
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add] at h
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.one_mul,
      htrace, mul_one]
    calc
      _ = ∑ p, (M.effect p * M.effect (l, a)).trace * (X * M.effect p).trace := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Matrix.trace_mul_comm (M.effect p) X]
        ring
      _ = _ := h

private def transition {d : ℕ} (S : SICFamily d) (M : MUBFamily d (d + 1)) :
    Matrix (Fin (d + 1) × Fin d) (Fin (d * d)) ℂ :=
  fun p i => ((d : ℂ) + 1) * (sicProjector S i * M.effect p).trace - 1

private theorem transition_real {d : ℕ} (S : SICFamily d) (M : MUBFamily d (d + 1))
    (p : Fin (d + 1) × Fin d) (i : Fin (d * d)) :
    star (transition S M p i) = transition S M p i := by
  have hP : (sicProjector S i).IsHermitian :=
    (Matrix.posSemidef_vecMulVec_self_star (S.1 i)).1
  have hG : (M.effect p).IsHermitian := by
    change (D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj
      (M.ket p.1 p.2)).IsHermitian
    rw [D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj_eq_outer]
    exact (Matrix.posSemidef_vecMulVec_self_star _).1
  have ht := D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian
    (sicProjector S i) (M.effect p) hP hG
  have hreal : star (sicProjector S i * M.effect p).trace =
      (sicProjector S i * M.effect p).trace := by
    rw [ht]
    exact Complex.conj_ofReal _
  simp only [transition, star_sub, star_mul, star_add, star_natCast, star_one, hreal]
  ring

private theorem transition_expansion {d : ℕ} (hd : 2 ≤ d) (S : SICFamily d)
    (M : MUBFamily d (d + 1)) (p : Fin (d + 1) × Fin d) :
    ∑ i, transition S M p i • sicEffect S i = M.effect p := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hE : ∑ i, sicEffect S i = 1 := by
    change ∑ i, (d : ℂ)⁻¹ • sicProjector S i = 1
    rw [← Finset.smul_sum, sicProjector_sum hd S, smul_smul,
      inv_mul_cancel₀ hd0, one_smul]
  have ht : ∑ i, (sicEffect S i * M.effect p).trace = 1 := by
    rw [← Matrix.trace_sum, ← Matrix.sum_mul, hE, Matrix.one_mul]
    exact MState.tr' (MState.pure (M.ket p.1 p.2))
  have hterm (i : Fin (d * d)) : transition S M p i • sicEffect S i =
      (sicEffect S i * M.effect p).trace • (((d : ℂ) + 1) • sicProjector S i) -
        (d : ℂ)⁻¹ • sicProjector S i := by
    simp only [transition, sicEffect, ← sicProjector.eq_def, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, smul_smul, ← sub_smul]
    congr 1
    ring
  calc
    _ = (∑ i, (sicEffect S i * M.effect p).trace •
        (((d : ℂ) + 1) • sicProjector S i)) - 1 := by
      simp only [hterm, Finset.sum_sub_distrib, ← Finset.smul_sum,
        sicProjector_sum hd S, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    _ = ∑ i, (sicEffect S i * M.effect p).trace •
        (((d : ℂ) + 1) • sicProjector S i - 1) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ht, one_smul]
    _ = M.effect p := sic_frame hd S (M.effect p)

private theorem transition_gram {d : ℕ} (hd : 2 ≤ d) (S : SICFamily d)
    (M : MUBFamily d (d + 1)) :
    (transition S M)ᴴ * transition S M = ((d : ℂ) * (d + 1)) • 1 := by
  classical
  have htrace (p : Fin (d + 1) × Fin d) : (M.effect p).trace = 1 :=
    MState.tr' (MState.pure (M.ket p.1 p.2))
  have hAll : ∑ p, M.effect p = ((d : ℂ) + 1) • 1 := by
    have h := mub_frame hd M 1
    simp only [Matrix.mul_one, htrace, one_smul, Matrix.trace_one, Fintype.card_fin] at h
    rw [h]
    module
  have hs (i : Fin (d * d)) :
      ∑ p, (sicProjector S i * M.effect p).trace = (d : ℂ) + 1 := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, hAll, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, sicProjector_trace, smul_eq_mul, mul_one]
  have hpair (i j : Fin (d * d)) :
      ∑ p, (sicProjector S i * M.effect p).trace * (sicProjector S j * M.effect p).trace =
      (sicProjector S i * sicProjector S j).trace + 1 := by
    have h := congrArg (fun N : Matrix (Fin d) (Fin d) ℂ =>
      (sicProjector S i * N).trace) (mub_frame hd M (sicProjector S j))
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul, sicProjector_trace, one_smul, Matrix.mul_add, Matrix.mul_one,
      Matrix.trace_add] at h
    calc
      _ = ∑ p, (M.effect p * sicProjector S j).trace *
          (sicProjector S i * M.effect p).trace := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Matrix.trace_mul_comm (M.effect p) (sicProjector S j)]
        ring
      _ = _ := h
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, transition_real,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  calc
    _ = ((d : ℂ) + 1) ^ 2 * ((sicProjector S i * sicProjector S j).trace + 1) -
        ((d : ℂ) + 1) * (d + 1) - ((d : ℂ) + 1) * (d + 1) +
        ((d : ℂ) + 1) * d := by
      calc
        _ = ∑ p, (((d : ℂ) + 1) ^ 2 *
            ((sicProjector S i * M.effect p).trace *
              (sicProjector S j * M.effect p).trace) -
            ((d : ℂ) + 1) * (sicProjector S i * M.effect p).trace -
            ((d : ℂ) + 1) * (sicProjector S j * M.effect p).trace + 1) := by
          apply Finset.sum_congr rfl
          intro p _
          dsimp only [transition]
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            hpair, hs, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
            mul_one]
    _ = _ := by
      rw [sicProjector_gram]
      by_cases hij : i = j <;> simp only [hij, ite_true, ite_false]
      <;> field_simp <;> ring

private theorem correlation_transition {dA dB : ℕ} (hdA : 2 ≤ dA) (hdB : 2 ≤ dB)
    (SA : SICFamily dA) (SB : SICFamily dB)
    (MA : MUBFamily dA (dA + 1)) (MB : MUBFamily dB (dB + 1))
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    mubCorrelation ρ MA MB =
      transition SA MA * sicCorrelation ρ SA SB * (transition SB MB)ᴴ := by
  ext p q
  change (ρ * (MA.effect p ⊗ₖ MB.effect q)).trace = _
  rw [← transition_expansion hdA SA MA p, ← transition_expansion hdB SB MB q]
  have hTensor :
      (∑ i, transition SA MA p i • sicEffect SA i) ⊗ₖ
        (∑ j, transition SB MB q j • sicEffect SB j) =
      ∑ i, ∑ j, (transition SA MA p i * transition SB MB q j) •
        (sicEffect SA i ⊗ₖ sicEffect SB j) := by
    change (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)
      (∑ i, transition SA MA p i • sicEffect SA i))
        (∑ j, transition SB MB q j • sicEffect SB j) = _
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (transition SB MB q j * transition SA MA p i) • _ = _
    rw [mul_comm]
    rfl
  rw [hTensor]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, transition_real,
    sicCorrelation, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem scaled_isometry_traceNorm
    {a b m n : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype m] [Fintype n]
    (U : Matrix m a ℂ) (V : Matrix n b ℂ) (X : Matrix a b ℂ)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hU : Uᴴ * U = ((α : ℂ) ^ 2) • 1)
    (hV : Vᴴ * V = ((β : ℂ) ^ 2) • 1) :
    traceNorm (U * X * Vᴴ) = α * β * traceNorm X := by
  classical
  let P := CFC.sqrt (Xᴴ * X)
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hPP : P * P = Xᴴ * X :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  have hβ0 : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hβ)
  have hgram : (U * X * Vᴴ)ᴴ * (U * X * Vᴴ) =
      ((α : ℂ) ^ 2) • (V * (Xᴴ * X) * Vᴴ) := by
    calc
      _ = V * Xᴴ * (Uᴴ * U) * X * Vᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = _ := by
        rw [hU]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hsquare :
      (((α / β : ℝ) : ℂ) • (V * P * Vᴴ)) *
        (((α / β : ℝ) : ℂ) • (V * P * Vᴴ)) =
      ((α : ℂ) ^ 2) • (V * (Xᴴ * X) * Vᴴ) := by
    have hVV : (V * P * Vᴴ) * (V * P * Vᴴ) =
        ((β : ℂ) ^ 2) • (V * (P * P) * Vᴴ) := by
      calc
        _ = V * P * (Vᴴ * V) * P * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hV]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hVV, smul_smul, hPP]
    congr 1
    rw [Complex.ofReal_div]
    field_simp
  have hpositive :
      (0 : Matrix n n ℂ) ≤ ((α / β : ℝ) : ℂ) • (V * P * Vᴴ) := by
    apply Matrix.PosSemidef.nonneg
    apply (hP.mul_mul_conjTranspose_same V).smul
    exact Complex.zero_le_real.mpr (div_nonneg hα.le hβ.le)
  have hroot := CFC.sqrt_unique (hsquare.trans hgram.symm) hpositive
  change (CFC.sqrt ((U * X * Vᴴ)ᴴ * (U * X * Vᴴ))).trace.re = _
  rw [hroot, Matrix.trace_smul, Matrix.trace_mul_cycle, hV, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul]
  change ((((α / β : ℝ) : ℂ) * ((β : ℂ) ^ 2 * P.trace))).re =
    α * β * P.trace.re
  have hscalar : ((α / β : ℝ) : ℂ) * (β : ℂ) ^ 2 = ((α * β : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul]
    field_simp
  rw [← mul_assoc, hscalar]
  simp only [Complex.re_ofReal_mul]

theorem result : claim := by
  intro dA dB hdA hdB SA SB MA MB ρ _hρ _htrace
  rw [correlation_transition hdA hdB SA SB MA MB ρ]
  apply scaled_isometry_traceNorm
  · positivity
  · positivity
  · rw [transition_gram hdA SA MA]
    congr 1
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_add,
      Complex.ofReal_one]
  · rw [transition_gram hdB SB MB]
    congr 1
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_add,
      Complex.ofReal_one]

end D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality
