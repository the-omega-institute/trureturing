/- GID: D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/RenyiCMILowAlphaRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.claim; result=D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.result; claim=D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.claim
   digest: An exact half-alpha counterexample to optimized SBW A-channel monotonicity. -/

import D5.S3.Quantum.Information.RenyiCMILocalChannelRefutation

/-!
admission_basis: open-problem-resolution (#17673; proposed Refuted settlement).
The only public mathematical conclusion is the literal low-alpha refutation.
Every helper below is consumed on its proof path. The frozen functional,
matrix powers, index order and Kraus action are imported without alteration.
Compilation and the scoped axiom report remain required for acceptance.

proof_shape: claim = definition; live_consumers: result
proof_shape: radical_sign = bind-only; live_consumers: strict_values
proof_shape: sym = definition; live_consumers: sym_pos, sym_sqrt, inputBlock, outputBlock, Sin, Sout, Cin, Cout
proof_shape: sym_pos = bind-only; live_consumers: sym_sqrt, rho_pos, tau_pos
proof_shape: blocks = definition; live_consumers: blocks_mul, blocks_psd, blocks_pos, rho, tau, blocks_half, Cin, Cout
proof_shape: blocks_mul = bind-only; live_consumers: blocks_half
proof_shape: blocks_psd = bind-only; live_consumers: blocks_pos, blocks_half
proof_shape: blocks_pos = bind-only; live_consumers: rho_pos, tau_pos
proof_shape: half_power = bind-only; live_consumers: quarter_power, sym_sqrt, blocks_half
proof_shape: quarter_power = bind-only; live_consumers: negative_quarter, Qin_power, Qout_power
proof_shape: negative_quarter = bind-only; live_consumers: exterior_power
proof_shape: sym_sqrt = bind-only; live_consumers: balanced_half, Sin_half
proof_shape: t = definition; live_consumers: x, Sin, Sout, inputBlock, outputBlock, Cin, Cout
proof_shape: x = definition; live_consumers: r, p, q, radical_relations, Zin, Zout, strict_values
proof_shape: r = definition; live_consumers: s, radical_relations, Sin
proof_shape: s = definition; live_consumers: aa, bb, radical_relations, Sin
proof_shape: p = definition; live_consumers: m, radical_relations
proof_shape: q = definition; live_consumers: n, radical_relations
proof_shape: m = definition; live_consumers: radical_relations, Sout, Cout, Zout
proof_shape: n = definition; live_consumers: radical_relations, Sout, Cin, Cout, Zin, Zout
proof_shape: aa = definition; live_consumers: Cin, Zin, inside_input, strict_values
proof_shape: bb = definition; live_consumers: Cin, Zin, inside_input, strict_values
proof_shape: radical_relations = bind-only; live_consumers: Sout_half, Sin_half, inside_input, inside_output, strict_values, Zout_pos
proof_shape: rd = definition; live_consumers: marginal_AE_input, Qin_power
proof_shape: h = definition; live_consumers: z, qd, Qout, Sin, Sout, normalization_relations
proof_shape: u = definition; live_consumers: v, Sin, normalization_relations
proof_shape: v = definition; live_consumers: qd, normalization_relations
proof_shape: z = definition; live_consumers: normalization_relations, exterior_power
proof_shape: normalization_relations = bind-only; live_consumers: Sout_half, Sin_half, Qin_power, Qout_power, exterior_power, inside_input, inside_output
proof_shape: qd = definition; live_consumers: Qin
proof_shape: Qin = definition; live_consumers: Qin_power, inside_input
proof_shape: Qout = definition; live_consumers: Qout_power, inside_output
proof_shape: eps = definition; live_consumers: Sin, Sout, inputBlock, outputBlock, Cin, Cout
proof_shape: Sout = definition; live_consumers: Sin, Sout_half, tau_half, inside_input, inside_output
proof_shape: Sin = definition; live_consumers: Sin_half, rho_half, inside_input
proof_shape: inputBlock = definition; live_consumers: rho, rho_pos, channel_action, Sin_half
proof_shape: outputBlock = definition; live_consumers: tau, tau_pos, channel_action, Sout_half
proof_shape: rho = definition; live_consumers: rho_pos, rho_trace, channel_action, marginal_AE_input, marginal_E_input, rho_half, inside_input, renyi_input, result
proof_shape: tau = definition; live_consumers: tau_pos, channel_action, marginal_AE_output, marginal_E_output, tau_half, inside_output, renyi_output
proof_shape: K = definition; live_consumers: K_complete, channel_action, result
proof_shape: rho_pos = bind-only; live_consumers: rho_half, result
proof_shape: tau_pos = bind-only; live_consumers: tau_half
proof_shape: rho_trace = bind-only; live_consumers: result
proof_shape: K_complete = bind-only; live_consumers: result
proof_shape: channel_action = bind-only; live_consumers: result
proof_shape: marginal_AE_input = bind-only; live_consumers: Qin_power
proof_shape: marginal_AE_output = bind-only; live_consumers: Qout_power
proof_shape: marginal_E_input = bind-only; live_consumers: inside_input
proof_shape: marginal_E_output = bind-only; live_consumers: inside_output
proof_shape: half_square = bind-only; live_consumers: blocks_half
proof_shape: blocks_half = bind-only; live_consumers: rho_half, tau_half
proof_shape: balanced_half = bind-only; live_consumers: Sout_half
proof_shape: Sout_half = bind-only; live_consumers: Sin_half, tau_half
proof_shape: Sin_half = bind-only; live_consumers: rho_half
proof_shape: rho_half = bind-only; live_consumers: inside_input
proof_shape: tau_half = bind-only; live_consumers: inside_output
proof_shape: ext_diagonal = bind-only; live_consumers: Qin_power
proof_shape: Qin_power = bind-only; live_consumers: inside_input
proof_shape: Qout_power = bind-only; live_consumers: inside_output
proof_shape: exterior_power = bind-only; live_consumers: inside_input, inside_output
proof_shape: inside = definition; live_consumers: inside_input, inside_output, renyi_input, renyi_output
proof_shape: Cin = definition; live_consumers: inside_input, Cin_herm, trace_input
proof_shape: Cout = definition; live_consumers: inside_output, Cout_herm, trace_output
proof_shape: Zin = definition; live_consumers: trace_input, renyi_input, strict_values, result
proof_shape: Zout = definition; live_consumers: trace_output, renyi_output, strict_values, Zout_pos, result
proof_shape: inside_input = bind-only; live_consumers: renyi_input
proof_shape: inside_output = bind-only; live_consumers: renyi_output
proof_shape: two_power = bind-only; live_consumers: renyi_input, renyi_output
proof_shape: Cin_herm = bind-only; live_consumers: renyi_input
proof_shape: Cout_herm = bind-only; live_consumers: renyi_output
proof_shape: trace_input = bind-only; live_consumers: renyi_input
proof_shape: trace_output = bind-only; live_consumers: renyi_output
proof_shape: renyi_input = bind-only; live_consumers: result
proof_shape: renyi_output = bind-only; live_consumers: result
proof_shape: strict_values = bind-only; live_consumers: result
proof_shape: Zout_pos = bind-only; live_consumers: result
proof_shape: result = bind-only; live_consumers: external-open-problem-resolution
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.RenyiCMILocalChannelRefutation

namespace D5.S3.Quantum.Information.RenyiCMILowAlphaRefutation

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The originally registered low-alpha assertion, with the frozen functional and channel. -/
def claim : Prop :=
  ∀ (dA dA' dB dE r : ℕ)
    (ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ)
    (K : Fin r → Matrix (Fin dA') (Fin dA) ℂ) (α : ℝ),
    ρ.PosSemidef → ρ.trace = 1 → ∑ j, (K j)ᴴ * K j = 1 →
    (0 < α ∧ α < 1) → renyiCMI α (applyA K ρ) ≤ renyiCMI α ρ

private lemma radical_sign (x r p q s m n A B : ℝ)
    (hx : 0 < x) (hxu : x ≤ 1 / 100000000)
    (hr : 0 < r) (hp : 0 < p) (hq : 0 < q)
    (hs : 0 < s) (hm : 0 < m) (hn : 0 < n)
    (hr2 : r ^ 2 = 1 - 289 * x) (hp2 : p ^ 2 = 1 - 64 * x)
    (hq2 : q ^ 2 = 1 - 576 * x) (hs2 : s ^ 2 = 17 + 8 * r)
    (hm2 : 2 * m ^ 2 = 1 + p) (hn2 : 2 * n ^ 2 = 1 + q)
    (hA : A = 5 * (s ^ 2 + 9) / (34 * s)) (hB : B = 4 / s) :
    (m - A) * (m + A + 2 * n) / 4 +
      4 * x * (1 / m - B) * (1 / m + B - 6 / n) < -(473 / 1000) * x := by
  have hrlo : (9999 / 10000 : ℝ) ≤ r := by nlinarith
  have hrhi : r ≤ 1 := by nlinarith
  have hplo : (9999 / 10000 : ℝ) ≤ p := by nlinarith
  have hphi : p ≤ 1 := by nlinarith
  have hslo : (49999 / 10000 : ℝ) ≤ s := by nlinarith
  have hshi : s ≤ 5 := by nlinarith
  have hmlo : (9999 / 10000 : ℝ) ≤ m := by nlinarith
  have hmhi : m ≤ 1 := by nlinarith
  have hqhi : q ≤ 1 := by nlinarith
  have hnhi : n ≤ 1 := by nlinarith
  have hAs : A * (34 * s) = 5 * (s ^ 2 + 9) := by
    rw [hA]; field_simp
  have hApos : 0 < A := by rw [hA]; positivity
  have hfact : (1 - A) * (34 * s) = (5 - s) * (5 * s - 9) := by
    nlinarith [hAs]
  have hAnonneg : 0 ≤ 1 - A := by
    apply nonneg_of_mul_nonneg_left (b := 34*s) ?_ (by positivity)
    rw [hfact]
    exact mul_nonneg (by linarith) (by linarith)
  have hAhi : A ≤ 1 := by linarith
  have hpair : (5 - s) * (s + 5) * (1 + r) = 2312 * x := by
    calc
      (5 - s) * (s + 5) * (1 + r) = 8 * (1 - r) * (1 + r) := by
        linear_combination -(1+r)*hs2
      _ = 2312 * x := by nlinarith [hr2]
  let d := s * (1 + r) * (s + 5)
  have hdlo : (9999 / 100 : ℝ) < d := by
    have h1 : (49999 / 10000 : ℝ) * (19999 / 10000) ≤ s * (1 + r) :=
      mul_le_mul hslo (by linarith) (by norm_num) (by positivity)
    have h2 : (49999 / 10000 : ℝ) * (19999 / 10000) * (99999 / 10000) ≤ d :=
      mul_le_mul h1 (by linarith) (by norm_num) (by positivity)
    exact lt_of_lt_of_le (by norm_num) h2
  have hAid : (1 - A) * d = 68 * x * (5 * s - 9) := by
    dsimp [d]
    linear_combination ((1 + r) * (s + 5) / 34) * hfact +
      ((5 * s - 9) / 34) * hpair
  have hnum : 68 * x * (5 * s - 9) ≤ 1088 * x := by nlinarith
  have hAx : 1 - A < (5441 / 500 : ℝ) * x := by
    have hmul : (9999 / 100 : ℝ) * (1 - A) ≤ (1 - A) * d := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hdlo.le hAnonneg
    nlinarith
  have hmprod : (1 - m) * ((1 + p) * (1 + m)) = 32 * x := by
    linear_combination -(1 + p) / 2 * hm2 - hp2 / 2
  have hmprodhi : (1 + p) * (1 + m) ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hphi) (sub_nonneg.mpr hmhi)]
  have hmx : 8 * x ≤ 1 - m := by
    have hmul := mul_le_mul_of_nonneg_left hmprodhi (sub_nonneg.mpr hmhi)
    nlinarith only [hmul,hmprod]
  have hma : m - A < (1441 / 500 : ℝ) * x := by linarith
  have hfpos : 0 < (m + A + 2 * n) / 4 := by positivity
  have hfhi : (m + A + 2 * n) / 4 ≤ 1 := by linarith
  have hfirst : (m - A) * (m + A + 2 * n) / 4 < (1441 / 500 : ℝ) * x := by
    calc
      (m - A) * (m + A + 2 * n) / 4 = (m - A) * ((m + A + 2 * n) / 4) := by ring
      _ < ((1441 / 500 : ℝ) * x) * ((m + A + 2 * n) / 4) :=
        mul_lt_mul_of_pos_right hma hfpos
      _ ≤ (1441 / 500 : ℝ) * x := mul_le_of_le_one_right (by positivity) hfhi
  have hBmul : B * s = 4 := by rw [hB]; field_simp
  have hBlo : (4 / 5 : ℝ) ≤ B := by rw [hB]; apply (le_div_iff₀ hs).mpr; nlinarith
  have hBhi : B ≤ (8001 / 10000 : ℝ) := by
    rw [hB]; apply (div_le_iff₀ hs).mpr; nlinarith
  have himlo : (1 : ℝ) ≤ 1 / m := by apply (le_div_iff₀ hm).mpr; linarith
  have himhi : 1 / m ≤ (1001 / 1000 : ℝ) := by
    apply (div_le_iff₀ hm).mpr; nlinarith
  have hinlo : (6 : ℝ) ≤ 6 / n := by apply (le_div_iff₀ hn).mpr; nlinarith
  have hDlo : (1999 / 10000 : ℝ) ≤ 1 / m - B := by linarith
  have hThi : 1 / m + B - 6 / n ≤ -(41989 / 10000 : ℝ) := by linarith
  have hDT : (1 / m - B) * (1 / m + B - 6 / n) ≤
      -(41989 / 10000 : ℝ) * (1999 / 10000) := by
    have h1 := mul_le_mul_of_nonneg_left hThi (by linarith : 0 ≤ 1 / m - B)
    nlinarith
  have hsecond : 4 * x * (1 / m - B) * (1 / m + B - 6 / n) ≤
      -(4 * (41989 / 10000 : ℝ) * (1999 / 10000)) * x := by
    have := mul_le_mul_of_nonneg_left hDT (by positivity : 0 ≤ 4 * x)
    nlinarith
  nlinarith

private def sym (a b u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), (u : ℂ); (u : ℂ), (b : ℂ)]

private lemma sym_pos (a b u : ℝ) (ha : 0 < a) (hdet : u ^ 2 < a * b) :
    (sym a b u).PosDef := by
  let L : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; (u / a : ℝ), 1]
  let D : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(a : ℂ), (b - u ^ 2 / a : ℝ)]
  have hD : D.PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i
    · simpa [D] using (show (0 : ℂ) < (a : ℂ) by exact_mod_cast ha)
    · have hb : 0 < b - u ^ 2 / a := by
        apply sub_pos.mpr
        exact (div_lt_iff₀ ha).mpr (by simpa [mul_comm] using hdet)
      simpa [D] using (show (0 : ℂ) < ((b - u ^ 2 / a : ℝ) : ℂ) by exact_mod_cast hb)
  have hL : Function.Injective L.vecMul := by
    intro v w h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [L, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h1
    funext i
    fin_cases i
    · simpa [h1] using h0
    · exact h1
  have he : L * D * Lᴴ = sym a b u := by
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, D, sym, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
        push_cast <;> field_simp [haC] <;> ring
  rw [← he]
  exact hD.mul_mul_conjTranspose_same hL

private def blocks {ι κ : Type*} [DecidableEq ι]
    (M : ι → Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  fun i j => if i.1 = j.1 then M i.1 i.2 j.2 else 0

private lemma blocks_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M N : ι → Matrix κ κ ℂ) : blocks M * blocks N = blocks (fun i => M i * N i) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i = j
  · subst j; simp [blocks, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [blocks, Matrix.mul_apply, Fintype.sum_prod_type, hij]

private lemma blocks_psd {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : ι → Matrix κ κ ℂ) (hM : ∀ i, (M i).PosSemidef) : (blocks M).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext ⟨i,k⟩ ⟨j,l⟩
    by_cases h : i = j
    · subst j; simpa [blocks, Matrix.conjTranspose_apply] using congrArg (fun X => X k l) (hM i).isHermitian.eq
    · simp [blocks, Matrix.conjTranspose_apply, h, Ne.symm h]
  · intro x
    have he : star x ⬝ᵥ (blocks M *ᵥ x) =
        ∑ i, star (fun k => x (i,k)) ⬝ᵥ (M i *ᵥ (fun k => x (i,k))) := by
      simp [blocks, dotProduct, Matrix.mulVec, Fintype.sum_prod_type]
    rw [he]
    exact Finset.sum_nonneg fun i _ => (hM i).dotProduct_mulVec_nonneg _

private lemma blocks_pos {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : ι → Matrix κ κ ℂ) (hM : ∀ i, (M i).PosDef) : (blocks M).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨(blocks_psd M (fun i => (hM i).posSemidef)).isHermitian, ?_⟩
  intro x hx
  have he : star x ⬝ᵥ (blocks M *ᵥ x) =
      ∑ i, star (fun k => x (i,k)) ⬝ᵥ (M i *ᵥ (fun k => x (i,k))) := by
    simp [blocks, dotProduct, Matrix.mulVec, Fintype.sum_prod_type]
  rw [he]
  obtain ⟨⟨i,k⟩, hik⟩ := Function.ne_iff.mp hx
  apply Finset.sum_pos'
  · intro j _; exact (hM j).posSemidef.dotProduct_mulVec_nonneg _
  · refine ⟨i, Finset.mem_univ _, (hM i).dotProduct_mulVec_pos ?_⟩
    intro hz
    exact hik (congrFun hz k)

private lemma half_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M S : Matrix ι ι ℂ) (hS : S.PosSemidef) (hsq : S * S = M) :
    mpow M (1 / 2) = S := by
  have hM : M.PosSemidef := by rw [← hsq]; simpa [pow_two] using hS.pow 2
  rw [mpow, ← CFC.rpow_eq_cfc_real hM.nonneg, ← CFC.sqrt_eq_rpow]
  exact CFC.sqrt_unique hsq hS.nonneg

private lemma quarter_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M Q : Matrix ι ι ℂ) (hQ : Q.PosSemidef) (hfour : (Q*Q)*(Q*Q) = M) :
    mpow M (1 / 4) = Q := by
  have hQQ : (Q*Q).PosSemidef := by simpa [pow_two] using hQ.pow 2
  have hM : M.PosSemidef := by rw [← hfour]; simpa [pow_two] using hQQ.pow 2
  have h2 := half_power M (Q*Q) hQQ hfour
  have h1 := half_power (Q*Q) Q hQ rfl
  calc
    mpow M (1/4) = mpow (mpow M (1/2)) (1/2) := by
      simp only [mpow, ← CFC.rpow_eq_cfc_real hM.nonneg]
      rw [← CFC.rpow_eq_cfc_real (CFC.rpow_nonneg (a := M) (y := (1/2 : ℝ)))]
      rw [CFC.rpow_rpow_of_exponent_nonneg M (1/2) (1/2) (by norm_num) (by norm_num) hM.nonneg]
      norm_num
    _ = Q := by rw [h2, h1]

private lemma negative_quarter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M Q J : Matrix ι ι ℂ) (hM : M.PosDef) (hQ : Q.PosSemidef)
    (hfour : (Q*Q)*(Q*Q) = M) (hQJ : Q*J=1) : mpow M (-1/4) = J := by
  have hquarter := quarter_power M Q hQ hfour
  have hinv : mpow M (-1/4) * Q = 1 := by
    rw [← hquarter, mpow, mpow, ← CFC.rpow_eq_cfc_real hM.posSemidef.nonneg,
      ← CFC.rpow_eq_cfc_real hM.posSemidef.nonneg]
    convert CFC.rpow_neg_mul_rpow (1/4 : ℝ) hM.isStrictlyPositive using 1 <;> congr 2 <;> ring
  calc
    mpow M (-1/4) = mpow M (-1/4) * (Q*J) := by rw [hQJ, Matrix.mul_one]
    _ = J := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

private lemma sym_sqrt (a b u d g : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (hg : 0 < g) (hd2 : d ^ 2 = a * b - u ^ 2)
    (hg2 : g ^ 2 = a + b + 2 * d) :
    mpow (sym a b u) (1 / 2) = sym ((a+d)/g) ((b+d)/g) (u/g) := by
  apply half_power
  · apply (sym_pos _ _ _ (by positivity) ?_).posSemidef
    rw [div_pow, div_mul_div_comm, ← pow_two]
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hg)).2
    nlinarith [mul_pos ha hd, mul_pos hb hd, sq_pos_of_pos hd]
  · have h00 : ((a+d)/g)*((a+d)/g) + (u/g)*(u/g) = a := by
      field_simp
      nlinarith [congrArg (fun z => a*z) hg2]
    have h11 : (u/g)*(u/g) + ((b+d)/g)*((b+d)/g) = b := by
      field_simp
      nlinarith [congrArg (fun z => b*z) hg2]
    have h01 : ((a+d)/g)*(u/g) + (u/g)*((b+d)/g) = u := by
      field_simp
      nlinarith [congrArg (fun z => u*z) hg2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sym, Matrix.mul_apply, Fin.sum_univ_two]
    · exact_mod_cast h00
    · exact_mod_cast h01
    · have he : (u/g)*((a+d)/g) + ((b+d)/g)*(u/g) = u := by
        nlinarith only [h01]
      exact_mod_cast he
    · exact_mod_cast h11

private def t : ℝ := 1 / 1073741824
private def x : ℝ := t ^ 2
private def r : ℝ := Real.sqrt (1 - 289*x)
private def s : ℝ := Real.sqrt (17 + 8*r)
private def p : ℝ := Real.sqrt (1 - 64*x)
private def q : ℝ := Real.sqrt (1 - 576*x)
private def m : ℝ := Real.sqrt ((1+p)/2)
private def n : ℝ := Real.sqrt ((1+q)/2)
private def aa : ℝ := 5*(s^2+9)/(34*s)
private def bb : ℝ := 4/s

private lemma radical_relations :
    0 < x ∧ x ≤ 1/100000000 ∧
    0 < r ∧ r^2=1-289*x ∧ 0 < s ∧ s^2=17+8*r ∧
    0 < p ∧ p^2=1-64*x ∧ 0 < q ∧ q^2=1-576*x ∧
    0 < m ∧ 2*m^2=1+p ∧ 0 < n ∧ 2*n^2=1+q := by
  have hx : 0 < x := by norm_num [x,t]
  have hxu : x ≤ (1/100000000 : ℝ) := by norm_num [x,t]
  have hr : 0 < r := Real.sqrt_pos.2 (by nlinarith : 0 < 1-289*x)
  have hp : 0 < p := Real.sqrt_pos.2 (by nlinarith : 0 < 1-64*x)
  have hq : 0 < q := Real.sqrt_pos.2 (by nlinarith : 0 < 1-576*x)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hm : 0 < m := Real.sqrt_pos.2 (by positivity)
  have hn : 0 < n := Real.sqrt_pos.2 (by positivity)
  refine ⟨hx,hxu,hr,?_,hs,?_,hp,?_,hq,?_,hm,?_,hn,?_⟩
  · exact Real.sq_sqrt (by nlinarith : 0 ≤ 1-289*x)
  · exact Real.sq_sqrt (by positivity : 0 ≤ 17+8*r)
  · exact Real.sq_sqrt (by nlinarith : 0 ≤ 1-64*x)
  · exact Real.sq_sqrt (by nlinarith : 0 ≤ 1-576*x)
  · have := Real.sq_sqrt (by positivity : 0 ≤ (1+p)/2); dsimp [m]; nlinarith
  · have := Real.sq_sqrt (by positivity : 0 ≤ (1+q)/2); dsimp [n]; nlinarith

private def rd (a : Fin 3) (e : Fin 2) : ℝ :=
  if a=0 then (if e=0 then 16/68 else 1/68)
  else if a=1 then (if e=0 then 1/68 else 16/68) else 1/4

private def h : ℝ := Real.sqrt 2
private def u : ℝ := Real.sqrt 68
private def v : ℝ := Real.sqrt (1/u)
private def z : ℝ := Real.sqrt h

private lemma normalization_relations :
    0 < h ∧ h^2=2 ∧ 0 < u ∧ u^2=68 ∧ 0 < v ∧ v^2*u=1 ∧ 0 < z ∧ z^2=h := by
  have hh : 0 < h := Real.sqrt_pos.2 (by norm_num)
  have hu : 0 < u := Real.sqrt_pos.2 (by norm_num)
  have hv : 0 < v := Real.sqrt_pos.2 (by positivity)
  have hz : 0 < z := Real.sqrt_pos.2 hh
  refine ⟨hh,Real.sq_sqrt (by norm_num),hu,Real.sq_sqrt (by norm_num),hv,?_,hz,?_⟩
  · have hv2 : v^2=1/u := Real.sq_sqrt (by positivity)
    rw [hv2]; field_simp
  · exact Real.sq_sqrt hh.le

private def qd (a : Fin 3) (e : Fin 2) : ℝ :=
  if a=0 then (if e=0 then 2*v else v)
  else if a=1 then (if e=0 then v else 2*v) else 1/h

private def Qin : Matrix ((Fin 3 × Fin 2) × Fin 2) ((Fin 3 × Fin 2) × Fin 2) ℂ :=
  diagonal (fun i => (qd i.1.1 i.2 : ℂ))

private def Qout : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  diagonal (fun _ => (1/h : ℝ))

private def eps (b : Fin 2) : ℝ := if b = 0 then 1 else -1

private def Sout (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a=0 then sym (m/(2*h)) (m/(2*h)) (2*eps b*t/(h*m))
  else sym (n/(2*h)) (n/(2*h)) (-6*eps b*t/(h*n))

private def Sin (a : Fin 3) (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a=0 then sym ((8/68+r/34)/(s/(h*u))) ((1/136+r/34)/(s/(h*u)))
    ((eps b*t/2)/(s/(h*u)))
  else if a=1 then sym ((1/136+r/34)/(s/(h*u))) ((8/68+r/34)/(s/(h*u)))
    ((eps b*t/2)/(s/(h*u)))
  else Sout 1 b

private def inputBlock (a : Fin 3) (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 then sym (8/68) (1/136) (eps b*t/2)
  else if a = 1 then sym (1/136) (8/68) (eps b*t/2)
  else sym (1/8) (1/8) (-3*eps b*t)

private def outputBlock (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  sym (1/8) (1/8) ((if a = 0 then 1 else -3)*eps b*t)

private def rho : Matrix ((Fin 3 × Fin 2) × Fin 2) ((Fin 3 × Fin 2) × Fin 2) ℂ :=
  blocks (fun ab => inputBlock ab.1 ab.2)

private def tau : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  blocks (fun ab => outputBlock ab.1 ab.2)

private def K (j : Fin 3) : Matrix (Fin 2) (Fin 3) ℂ :=
  fun a c => if c = j ∧ a = (if j = 2 then 1 else 0) then 1 else 0

private lemma rho_pos : rho.PosDef := by
  apply blocks_pos
  intro ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> norm_num [inputBlock, eps, t]
  all_goals apply sym_pos <;> norm_num

private lemma tau_pos : tau.PosDef := by
  apply blocks_pos
  intro ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> norm_num [outputBlock, eps, t]
  all_goals apply sym_pos <;> norm_num

private lemma rho_trace : rho.trace = 1 := by
  norm_num [Matrix.trace, Matrix.diag, rho, blocks, inputBlock, sym,
    Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two]

private lemma K_complete : ∑ j, (K j)ᴴ * K j = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Fin.sum_univ_two, Matrix.one_apply]

private lemma channel_action : applyA K rho = tau := by
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨c,d⟩,f⟩
  fin_cases a <;> fin_cases c <;> fin_cases b <;> fin_cases d <;>
    fin_cases e <;> fin_cases f <;>
    norm_num [applyA, K, rho, tau, blocks, inputBlock, outputBlock, sym, eps,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two]

private lemma marginal_AE_input : margAE rho = diagonal (fun ae => (rd ae.1 ae.2 : ℂ)) := by
  ext ⟨a,e⟩ ⟨c,f⟩
  fin_cases a <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    norm_num [margAE, partialTraceLeft, rho, blocks, inputBlock, sym, rd, eps,
      Fin.sum_univ_two, Matrix.diagonal] <;> ring

private lemma marginal_AE_output : margAE tau = (1/4 : ℂ) • 1 := by
  ext ⟨a,e⟩ ⟨c,f⟩
  fin_cases a <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    norm_num [margAE, partialTraceLeft, tau, blocks, outputBlock, sym, eps,
      Fin.sum_univ_two, Matrix.one_apply]

private lemma marginal_E_input : margE rho = (1/2 : ℂ) • 1 := by
  ext e f
  fin_cases e <;> fin_cases f <;>
    norm_num [margE, partialTraceLeft, rho, blocks, inputBlock, sym, eps,
      Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_prod_type, Matrix.one_apply] <;> ring

private lemma marginal_E_output : margE tau = (1/2 : ℂ) • 1 := by
  ext e f
  fin_cases e <;> fin_cases f <;>
    norm_num [margE, partialTraceLeft, tau, blocks, outputBlock, sym, eps,
      Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.one_apply]

private lemma half_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    mpow M (1/2) * mpow M (1/2) = M := by
  rw [mpow, ← CFC.rpow_eq_cfc_real hM.nonneg, ← CFC.sqrt_eq_rpow]
  exact CFC.sqrt_mul_sqrt_self M hM.nonneg

private lemma blocks_half {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : ι → Matrix κ κ ℂ)
    (hM : ∀ i, (M i).PosSemidef) :
    mpow (blocks M) (1/2) = blocks (fun i => mpow (M i) (1/2)) := by
  apply half_power
  · apply blocks_psd
    intro i
    rw [mpow, ← CFC.rpow_eq_cfc_real (hM i).nonneg]
    exact CFC.rpow_nonneg.posSemidef
  · rw [blocks_mul]
    congr 1
    funext i
    exact half_square (M i) (hM i)

private lemma balanced_half (k e T c w H : ℝ) (hH : 0 < H) (hH2 : H^2=2)
    (he : e^2=1) (hc : 0 < c) (hw : 0 < w)
    (hc2 : c^2=1-64*k^2*T^2) (hw2 : 2*w^2=1+c) :
    mpow (sym (1/8) (1/8) (k*e*T)) (1/2) =
      sym (w/(2*H)) (w/(2*H)) (2*k*e*T/(H*w)) := by
  have hd : (c/8)^2 = (1/8 : ℝ)*(1/8)-(k*e*T)^2 := by
    nlinarith [congrArg (fun a => k^2*T^2*a) he]
  have hg : (w/H)^2 = (1/8 : ℝ)+(1/8)+2*(c/8) := by
    rw [div_pow, hH2]; nlinarith
  rw [sym_sqrt _ _ _ (c/8) (w/H) (by norm_num) (by norm_num)
    (by positivity) (by positivity) hd hg]
  congr 1 <;> field_simp [hH.ne',hw.ne'] <;>
    nlinarith [hH2,hw2,congrArg (fun y : ℝ => k*e*T*y) hH2]

private lemma Sout_half (a b : Fin 2) : mpow (outputBlock a b) (1/2) = Sout a b := by
  rcases radical_relations with ⟨hx,hxu,hr,hr2,hs,hs2,hp,hp2,hq,hq2,hm,hm2,hn,hn2⟩
  rcases normalization_relations with ⟨hh,hh2,hu,hu2,hv,hv2,hz,hz2⟩
  have he : (eps b)^2=1 := by fin_cases b <;> norm_num [eps]
  fin_cases a
  · simpa [outputBlock,Sout] using balanced_half 1 (eps b) t p m h hh hh2 he hp hm
      (by simpa [x] using hp2) hm2
  · convert balanced_half (-3) (eps b) t q n h hh hh2 he hq hn
      (by norm_num [x] at hq2 ⊢; nlinarith [hq2]) hn2 using 1 <;>
      norm_num [outputBlock,Sout] <;> ring

private lemma Sin_half (a : Fin 3) (b : Fin 2) : mpow (inputBlock a b) (1/2) = Sin a b := by
  rcases radical_relations with ⟨hx,hxu,hr,hr2,hs,hs2,hp,hp2,hq,hq2,hm,hm2,hn,hn2⟩
  rcases normalization_relations with ⟨hh,hh2,hu,hu2,hv,hv2,hz,hz2⟩
  have he : (eps b)^2=1 := by fin_cases b <;> norm_num [eps]
  have hd : (r/34)^2 = (8/68 : ℝ)*(1/136)-(eps b*t/2)^2 := by
    dsimp [x] at hr2
    nlinarith [congrArg (fun a => t^2*a) he]
  have hg : (s/(h*u))^2 = (8/68 : ℝ)+(1/136)+2*(r/34) := by
    rw [div_pow,mul_pow,hh2,hu2]; nlinarith
  fin_cases a
  · simpa [inputBlock,Sin] using sym_sqrt (8/68) (1/136) (eps b*t/2) (r/34)
      (s/(h*u)) (by norm_num) (by norm_num) (by positivity) (by positivity) hd hg
  · simpa [inputBlock,Sin,add_comm,mul_comm] using
      sym_sqrt (1/136) (8/68) (eps b*t/2) (r/34) (s/(h*u))
        (by norm_num) (by norm_num) (by positivity) (by positivity) (by simpa [mul_comm] using hd)
        (by simpa [add_comm] using hg)
  · simpa [inputBlock,outputBlock,Sin] using Sout_half 1 b

private lemma rho_half : mpow rho (1/2) = blocks (fun ab => Sin ab.1 ab.2) := by
  rw [rho, blocks_half]
  · congr 1; funext ab; exact Sin_half ab.1 ab.2
  · intro ⟨a,b⟩
    have he : rho.submatrix (fun e : Fin 2 => ((a,b),e)) (fun e : Fin 2 => ((a,b),e)) =
        inputBlock a b := by
      ext e f
      simp [rho,blocks,Matrix.submatrix]
    rw [← he]
    exact rho_pos.posSemidef.submatrix (fun e : Fin 2 => ((a,b),e))

private lemma tau_half : mpow tau (1/2) = blocks (fun ab => Sout ab.1 ab.2) := by
  rw [tau, blocks_half]
  · congr 1; funext ab; exact Sout_half ab.1 ab.2
  · intro ⟨a,b⟩
    have he : tau.submatrix (fun e : Fin 2 => ((a,b),e)) (fun e : Fin 2 => ((a,b),e)) =
        outputBlock a b := by
      ext e f
      simp [tau,blocks,Matrix.submatrix]
    rw [← he]
    exact tau_pos.posSemidef.submatrix (fun e : Fin 2 => ((a,b),e))

private lemma ext_diagonal {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E] (d : A × E → ℂ) :
    extAE (B:=B) (diagonal d) = diagonal (fun i => d (i.1.1,i.2)) := by
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨c,f⟩,g⟩
  simp only [extAE,Matrix.of_apply,Matrix.diagonal,Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma Qin_power : mpow (extAE (B:=Fin 2) (margAE rho)) (1/4) = Qin := by
  rcases normalization_relations with ⟨hh,hh2,hu,hu2,hv,hv2,hz,hz2⟩
  have hv4 : v^4=(1/68 : ℝ) := by
    have he := congrArg (fun a : ℝ => a^2) hv2
    rw [mul_pow,hu2] at he
    nlinarith [he]
  rw [marginal_AE_input,ext_diagonal]
  apply quarter_power
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro ⟨⟨a,b⟩,e⟩
    fin_cases a <;> fin_cases e <;> simp [Qin,qd]
    all_goals positivity
  · simp only [Qin,diagonal_mul_diagonal]
    congr 1
    funext ⟨⟨a,b⟩,e⟩
    have he : (qd a e * qd a e)*(qd a e * qd a e) = rd a e := by
      have hh4 : h^4=4 := by nlinarith [congrArg (fun a : ℝ => a^2) hh2]
      fin_cases a <;> fin_cases e <;> norm_num [qd,rd] <;>
        field_simp [hh.ne'] <;> nlinarith [hv4,hh4]
    exact_mod_cast he

private lemma Qout_power : mpow (extAE (B:=Fin 2) (margAE tau)) (1/4) = Qout := by
  rcases normalization_relations with ⟨hh,hh2,hu,hu2,hv,hv2,hz,hz2⟩
  have he : extAE (B:=Fin 2) (margAE tau) =
      diagonal (fun _ : (Fin 2 × Fin 2) × Fin 2 => (1/4 : ℂ)) := by
    rw [marginal_AE_output]
    ext ⟨⟨a,b⟩,e⟩ ⟨⟨c,d⟩,f⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases e <;> fin_cases f <;> norm_num [extAE,Matrix.diagonal,Matrix.one_apply]
  rw [he]
  apply quarter_power
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    change (0 : ℂ) ≤ ((1/h : ℝ) : ℂ)
    positivity
  · simp only [Qout,diagonal_mul_diagonal]
    congr 1
    funext i
    have hh4 : h^4=4 := by nlinarith [congrArg (fun a : ℝ => a^2) hh2]
    have he : ((1/h)*(1/h))*((1/h)*(1/h)) = (1/4 : ℝ) := by
      field_simp [hh.ne']
      nlinarith [hh4]
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg (fun a : ℝ => (a : ℂ)) he

private lemma exterior_power :
    mpow (extE (B:=Fin 2) ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) (-1/4) =
      diagonal (fun _ : Fin 2 × Fin 2 => (z : ℂ)) := by
  rcases normalization_relations with ⟨hh,hh2,hu,hu2,hv,hv2,hz,hz2⟩
  have he : extE (B:=Fin 2) ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      diagonal (fun _ : Fin 2 × Fin 2 => (1/2 : ℂ)) := by
    ext ⟨b,e⟩ ⟨c,f⟩
    fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
      norm_num [extE,Matrix.kroneckerMap_apply,Matrix.diagonal,Matrix.one_apply]
  rw [he]
  apply negative_quarter _ (diagonal (fun _ : Fin 2 × Fin 2 => ((1/z : ℝ) : ℂ)))
  · exact Matrix.posDef_diagonal_iff.mpr (by intro i; norm_num)
  · exact Matrix.posSemidef_diagonal_iff.mpr (by intro i; positivity)
  · simp only [diagonal_mul_diagonal]
    congr 1
    funext i
    have hz4 : z^4=2 := by nlinarith [hz2,congrArg (fun a : ℝ => a^2) hz2]
    have he : ((1/z)*(1/z))*((1/z)*(1/z)) = (1/2 : ℝ) := by
      field_simp [hz.ne']
      nlinarith [hz4]
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg (fun a : ℝ => (a : ℂ)) he
  · simp only [diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 1
    congr 1
    funext i
    have he : (1/z)*z = (1 : ℝ) := by field_simp [hz.ne']
    exact_mod_cast he

private def inside {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : Matrix ((A × Fin 2) × Fin 2) ((A × Fin 2) × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  mpow (extE (B:=Fin 2) (margE ρ)) (-1/4) *
    traceA (mpow (extAE (B:=Fin 2) (margAE ρ)) (1/4) * mpow ρ (1/2) *
      mpow (extAE (B:=Fin 2) (margAE ρ)) (1/4)) *
    mpow (extE (B:=Fin 2) (margE ρ)) (-1/4)

private def Cin : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  blocks (fun b => sym ((aa+n)/4) ((aa+n)/4) (eps b*t*(bb-3/n)))

private def Cout : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  blocks (fun b => sym ((m+n)/4) ((m+n)/4) (eps b*t*(1/m-3/n)))

private def Zin : ℝ := (aa+n)^2/4+4*x*(bb-3/n)^2
private def Zout : ℝ := (m+n)^2/4+4*x*(1/m-3/n)^2

private lemma inside_input : inside rho = Cin := by
  rcases radical_relations with ⟨hx,hxu,hr,hr2,hs,hs2,hp,hp2,hq,hq2,hm,hm2,hn,hn2⟩
  rcases normalization_relations with ⟨hh,hh2,hu,hu2,hv,hv2,hz,hz2⟩
  have hv2' : v^2=1/u := (eq_div_iff hu.ne').2 hv2
  have hvC : (v : ℂ)^2=1/(u : ℂ) := by exact_mod_cast hv2'
  have hzC : (z : ℂ)^2=(h : ℂ) := by exact_mod_cast hz2
  have hhC : (h : ℂ)^2=2 := by exact_mod_cast hh2
  have hh3C : (h : ℂ)^3=2*(h : ℂ) := by
    calc
      (h : ℂ)^3 = (h : ℂ)^2*(h : ℂ) := by ring
      _ = 2*(h : ℂ) := by rw [hhC]
  have hh4C : (h : ℂ)^4=4 := by
    calc
      (h : ℂ)^4 = ((h : ℂ)^2)^2 := by ring
      _ = 4 := by rw [hhC]; norm_num
  have huC : (u : ℂ)^2=68 := by exact_mod_cast hu2
  have hsC : (s : ℂ)^2=17+8*(r : ℂ) := by exact_mod_cast hs2
  have hhn : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hun : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hsn : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hnn : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  rw [inside,marginal_E_input,exterior_power,Qin_power,rho_half]
  ext ⟨b,e⟩ ⟨c,f⟩
  fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    simp [Cin,traceA,partialTraceLeft,Qin,Sin,Sout,blocks,qd,eps,sym,
      Matrix.mul_apply,Matrix.diagonal,Fintype.sum_prod_type,Fin.sum_univ_two,
      Fin.sum_univ_three,aa,bb]
  all_goals
    push_cast <;>
    field_simp [hhn,hun,hsn,hnn] <;>
    ring_nf <;>
    simp only [hvC,hzC,hhC,hh3C,hh4C,huC,hsC] <;>
    field_simp [hun] <;>
    ring_nf <;>
    simp [hvC,hzC,hhC,hh3C,hh4C,huC,hsC] <;> ring

private lemma inside_output : inside tau = Cout := by
  rcases radical_relations with ⟨hx,hxu,hr,hr2,hs,hs2,hp,hp2,hq,hq2,hm,hm2,hn,hn2⟩
  rcases normalization_relations with ⟨hh,hh2,hu,hu2,hv,hv2,hz,hz2⟩
  have hzC : (z : ℂ)^2=(h : ℂ) := by exact_mod_cast hz2
  have hhC : (h : ℂ)^2=2 := by exact_mod_cast hh2
  have hh3C : (h : ℂ)^3=2*(h : ℂ) := by
    calc
      (h : ℂ)^3 = (h : ℂ)^2*(h : ℂ) := by ring
      _ = 2*(h : ℂ) := by rw [hhC]
  have hhn : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hmn : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hnn : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  rw [inside,marginal_E_output,exterior_power,Qout_power,tau_half]
  ext ⟨b,e⟩ ⟨c,f⟩
  fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    simp [Cout,traceA,partialTraceLeft,Qout,Sout,blocks,eps,sym,
      Matrix.mul_apply,Matrix.diagonal,Fintype.sum_prod_type,Fin.sum_univ_two]
  all_goals
    push_cast <;>
    field_simp [hhn,hmn,hnn] <;>
    ring_nf <;>
    simp [hzC,hhC,hh3C] <;> ring

private lemma two_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) : mpow M 2 = M*M := by
  have hf : (fun t : ℝ => t^(2:ℝ)) = (fun t : ℝ => t^(2:ℕ)) := by
    funext t; exact Real.rpow_natCast t 2
  rw [mpow,hf,cfc_pow_id M 2 hM.isSelfAdjoint,pow_two]

private lemma Cin_herm : Cin.IsHermitian := by
  ext ⟨b,e⟩ ⟨c,f⟩
  fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    simp [Cin,blocks,sym,Matrix.conjTranspose_apply]

private lemma Cout_herm : Cout.IsHermitian := by
  ext ⟨b,e⟩ ⟨c,f⟩
  fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    simp [Cout,blocks,sym,Matrix.conjTranspose_apply]

private lemma trace_input : (Matrix.trace (Cin*Cin)).re=Zin := by
  simp [Cin,blocks,sym,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two,eps,Zin,x]
  ring

private lemma trace_output : (Matrix.trace (Cout*Cout)).re=Zout := by
  simp [Cout,blocks,sym,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two,eps,Zout,x]
  ring

private lemma renyi_input : renyiCMI (1/2) rho = -Real.log Zin := by
  have he : renyiCMI (1/2) rho = -Real.log (Matrix.trace (mpow (inside rho) 2)).re := by
    norm_num [renyiCMI,inside]
  rw [he,inside_input,two_power _ Cin_herm,trace_input]

private lemma renyi_output : renyiCMI (1/2) tau = -Real.log Zout := by
  have he : renyiCMI (1/2) tau = -Real.log (Matrix.trace (mpow (inside tau) 2)).re := by
    norm_num [renyiCMI,inside]
  rw [he,inside_output,two_power _ Cout_herm,trace_output]

private lemma strict_values : Zout < Zin := by
  rcases radical_relations with ⟨hx,hxu,hr,hr2,hs,hs2,hp,hp2,hq,hq2,hm,hm2,hn,hn2⟩
  have hc := radical_sign x r p q s m n aa bb hx hxu hr hp hq hs hm hn
    hr2 hp2 hq2 hs2 hm2 hn2 rfl rfl
  have hid : Zout-Zin=(m-aa)*(m+aa+2*n)/4+4*x*(1/m-bb)*(1/m+bb-6/n) := by
    dsimp [Zout,Zin]; ring
  nlinarith

private lemma Zout_pos : 0 < Zout := by
  rcases radical_relations with ⟨hx,hxu,hr,hr2,hs,hs2,hp,hp2,hq,hq2,hm,hm2,hn,hn2⟩
  have h1 : 0 < (m+n)^2/4 := by positivity
  have h2 : 0 ≤ 4*x*(1/m-3/n)^2 := by positivity
  exact add_pos_of_pos_of_nonneg h1 h2

theorem result : ¬ claim := by
  intro hc
  have hdpi := hc 3 2 2 2 3 rho K (1/2) rho_pos.posSemidef rho_trace K_complete (by norm_num)
  rw [channel_action,renyi_input,renyi_output] at hdpi
  have hlog : Real.log Zout < Real.log Zin := Real.log_lt_log Zout_pos strict_values
  linarith

end

end D5.S3.Quantum.Information.RenyiCMILowAlphaRefutation
