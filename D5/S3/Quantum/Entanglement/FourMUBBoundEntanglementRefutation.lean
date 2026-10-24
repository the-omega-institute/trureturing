/- GID: D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.claim; result=D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.result; claim=D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.claim
   digest: Four mutually unbiased bases refute the dimension-eight necessity bound. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#16454; Refuted).
Direct frozen dependencies:
  StructuredNegativityCoincidenceRefutation.IsDensity
    statement_id: sha256:0386217fa1109c4358c01b5fe2db195888fa2f776c05e63cec2e880416d1c8ff
  StructuredNegativityCoincidenceRefutation.partialTransposeB
    statement_id: sha256:894491a0350c31f846bcfc59cbb3e13f12eb0801f6a00517db381f0dc0ecc393
  ConditionalHockeyStickOrthogonalReduction.posSemidef_blockDiagonal (public owner)
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The projector expression is inlined using Matrix.vecMulVec and star; no duplicate projector is declared.
Each private theorem has proof_shape: bind-only and escape_witness: none.
The consumers are the immediately following derivations of MUB orthogonality,
LDL positivity, partial-transpose positivity and the exact witness expectation.
-/
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import Mathlib.Data.LawfulXor.Basic

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3000
namespace D5.S3.Quantum.Entanglement.FourMUBBoundEntanglementRefutation
open Matrix
open scoped ComplexOrder
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (posSemidef_blockDiagonal)
noncomputable section
/-- Columns are basis vectors; basis zero is computational whenever present. -/
def IsMUBFamily {d m : ℕ} (U : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ α, U α ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
  (∀ hm : 0 < m, U ⟨0, hm⟩ = 1) ∧
  (∀ α β, α ≠ β → ∀ i j, ‖((U α)ᴴ * U β) i j‖ ^ 2 = 1 / (d : ℝ))

/-- The partial transpose of source Eq. (4), with the addition in Fin d. -/
noncomputable def witnessGamma {d m : ℕ}
    (U : Fin m → Matrix (Fin d) (Fin d) ℂ) (s : Fin d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (((d : ℂ) + (m : ℂ) - 1) / (d : ℂ)) • 1 -
    (∑ l : Fin d, Matrix.single (l, l + s) (l, l + s) (1 : ℂ)) -
    ∑ α ∈ (Finset.univ : Finset (Fin m)).filter (fun α => α.val ≠ 0),
      ∑ i : Fin d, Matrix.kronecker ((Matrix.vecMulVec (fun x => U α x i) (star (fun x => U α x i))))
        (((Matrix.vecMulVec (fun x => U α x i) (star (fun x => U α x i)))).map (star : ℂ → ℂ))

def DetectsBoundEntanglement {d m : ℕ}
    (U : Fin m → Matrix (Fin d) (Fin d) ℂ) (s : Fin d) : Prop :=
  ∃ ρ, IsDensity ρ ∧ (partialTransposeB ρ).PosSemidef ∧
    (Matrix.trace (witnessGamma U s * ρ)).re < 0

def claim : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ m : ℕ, m < 2 ^ (r - 1) + 1 →
    ∀ (U : Fin m → Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℂ),
      IsMUBFamily U → ∀ s : Fin (2 ^ r), ¬ DetectsBoundEntanglement U s

private def walsh (x k : Fin 8) : ℤ :=
  (-1) ^ ((x.val % 2) * (k.val % 2) +
    (x.val / 2 % 2) * (k.val / 2 % 2) +
    (x.val / 4 % 2) * (k.val / 4 % 2))
private def phase : Fin 3 → Fin 8 → ℂ :=
  ![fun _ => 1,
    ![1,1,Complex.I,Complex.I,Complex.I,-Complex.I,-1,1],
    ![1,1,1,-1,Complex.I,Complex.I,-Complex.I,Complex.I]]
private def gram (α β : Fin 3) (t : Fin 8) : ℂ :=
  ∑ x : Fin 8, star (phase α x) * phase β x * (walsh x t : ℂ)
private def scaledBasis (α : Fin 3) : Matrix (Fin 8) (Fin 8) ℂ :=
  fun x k => (((Real.sqrt 8)⁻¹ : ℝ) : ℂ) * phase α x * (walsh x k : ℂ)
private def fourBases : Fin 4 → Matrix (Fin 8) (Fin 8) ℂ :=
  ![1, scaledBasis 0, scaledBasis 1, scaledBasis 2]

private theorem walsh_product (x k l : Fin 8) :
    walsh x k * walsh x l = walsh x (Fin.xor k l) := by
  revert x k l
  decide
private theorem xor_zero (k l : Fin 8) : Fin.xor k l = 0 ↔ k = l := by
  exact xor_eq_zero_iff (α := Fin (2 ^ 3))
private theorem phase_normSq (α : Fin 3) (x : Fin 8) :
    Complex.normSq (phase α x) = 1 := by
  fin_cases α <;> fin_cases x <;> norm_num [phase, Complex.normSq_apply]
private theorem gram_same (α : Fin 3) (t : Fin 8) :
    gram α α t = if t = 0 then 8 else 0 := by
  fin_cases α <;> fin_cases t <;>
    apply Complex.ext <;>
    norm_num [gram, phase, walsh, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem gram_distinct (α β : Fin 3) (h : α ≠ β) (t : Fin 8) :
    Complex.normSq (gram α β t) = 8 := by
  fin_cases α <;> fin_cases β <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases t
  all_goals norm_num [gram, phase, walsh, Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
theorem scale_sq : (Real.sqrt 8)⁻¹ ^ 2 = 1 / 8 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num
private theorem gram_scaled (α β : Fin 3) (k l : Fin 8) :
    ((scaledBasis α)ᴴ * scaledBasis β) k l =
      (((Real.sqrt 8)⁻¹ : ℝ) : ℂ)^2 * gram α β (Fin.xor k l) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, scaledBasis, gram,
    star_mul, Complex.star_def, Complex.conj_ofReal, map_intCast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hw : (walsh x k : ℂ) * (walsh x l : ℂ) =
      (walsh x (Fin.xor k l) : ℂ) := by exact_mod_cast walsh_product x k l
  rw [← hw]
  ring

theorem scale_complex_sq : (((Real.sqrt 8)⁻¹ : ℝ) : ℂ)^2 = 1 / 8 := by
  rw [← Complex.ofReal_pow, scale_sq]
  norm_num
private theorem scaledBasis_unitary (α : Fin 3) :
    scaledBasis α ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext k l
  rw [gram_scaled, gram_same, scale_complex_sq]
  simp [xor_zero, Matrix.one_apply]
private theorem walsh_normSq (x k : Fin 8) : Complex.normSq (walsh x k : ℂ) = 1 := by
  have h : walsh x k * walsh x k = 1 := by
    rw [walsh_product, (xor_zero k k).2 rfl]
    rfl
  rw [Complex.normSq_intCast]
  exact_mod_cast h
private theorem scaledBasis_entry_norm (α : Fin 3) (x k : Fin 8) :
    Complex.normSq (scaledBasis α x k) = 1/8 := by
  simp only [scaledBasis, Complex.normSq_mul, Complex.normSq_ofReal,
    phase_normSq, walsh_normSq, mul_one]
  nlinarith [scale_sq]
private theorem scaledBasis_unbiased (α β : Fin 3) (h : α ≠ β) (k l : Fin 8) :
    ‖((scaledBasis α)ᴴ * scaledBasis β) k l‖ ^ 2 = 1/8 := by
  rw [Complex.sq_norm, gram_scaled, scale_complex_sq, Complex.normSq_mul,
    gram_distinct α β h]
  norm_num [Complex.normSq_apply]

private theorem fourBases_mub : IsMUBFamily fourBases := by
  refine ⟨?_, ?_, ?_⟩
  · intro α
    fin_cases α <;> simp [fourBases, scaledBasis_unitary]
  · intro hm
    rfl
  · intro α β h k l
    fin_cases α <;> fin_cases β
    all_goals try exact False.elim (h rfl)
    all_goals norm_num [fourBases, Fin.reduceFinMk]
    · simpa only [Complex.sq_norm] using scaledBasis_entry_norm 0 k l
    · simpa only [Complex.sq_norm] using scaledBasis_entry_norm 1 k l
    · simpa only [Complex.sq_norm] using scaledBasis_entry_norm 2 k l
    · simpa only [Matrix.conjTranspose_apply, Complex.sq_norm, starRingEnd_apply,
        Complex.star_def, Complex.normSq_conj] using scaledBasis_entry_norm 0 l k
    · exact scaledBasis_unbiased 0 1 (by decide) k l
    · exact scaledBasis_unbiased 0 2 (by decide) k l
    · simpa only [Matrix.conjTranspose_apply, Complex.sq_norm, starRingEnd_apply,
        Complex.star_def, Complex.normSq_conj] using scaledBasis_entry_norm 1 l k
    · exact scaledBasis_unbiased 1 0 (by decide) k l
    · exact scaledBasis_unbiased 1 2 (by decide) k l
    · simpa only [Matrix.conjTranspose_apply, Complex.sq_norm, starRingEnd_apply,
        Complex.star_def, Complex.normSq_conj] using scaledBasis_entry_norm 2 l k
    · exact scaledBasis_unbiased 2 0 (by decide) k l
    · exact scaledBasis_unbiased 2 1 (by decide) k l

private def blockA (p : Fin 2) (h : Fin 8) : Matrix (Fin 4) (Fin 4) ℂ :=
  match p.val with
  | 0 => match h.val with
    | 0 => !![127, 127, 127, 125; 127, 131, 129, 127; 127, 129, 131, 127; 125, 127, 127, 127]
    | 1 => !![603, 127, 54, 37; 127, 35, 37, 9; 54, 37, 603, 127; 37, 9, 127, 35]
    | 2 => !![123, 30, 39, -51; 30, 123, -51, 39; 39, -51, 135, 45; -51, 39, 45, 135]
    | 3 => !![118, 39, -68, 36; 39, 227, 42, -15; -68, 42, 101, 36; 36, -15, 36, 147]
    | 4 => !![127, 39, 37, -48; 39, 131, -54, 37; 37, -54, 131, 39; -48, 37, 39, 127]
    | 5 => !![109, 39, 107, 39; 39, 161, 39, 159; 107, 39, 109, 39; 39, 159, 39, 161]
    | 6 => !![129, -62, -51, 127; -62, 129, 127, -51; -51, 127, 129, -40; 127, -51, -40, 129]
    | _ => !![106, -47, 55, 35; -47, 155, 37, 10; 55, 37, 114, -54; 35, 10, -54, 219]
  | _ => match h.val with
    | 0 => !![127, 127, 39, 36; 127, 131, 42, 39; 39, 42, 131, 127; 36, 39, 127, 127]
    | 1 => !![603, 127, -68, -51; 127, 35, -51, -15; -68, -51, 603, 127; -51, -15, 127, 35]
    | 2 => !![123, 39, 127, 37; 39, 123, 37, 127; 127, 37, 135, 36; 37, 127, 36, 135]
    | 3 => !![118, 30, 54, 125; 30, 227, 129, 9; 54, 129, 101, 45; 125, 9, 45, 147]
    | 4 => !![127, 39, -51, 35; 39, 131, 37, -51; -51, 37, 131, 39; 35, -51, 39, 127]
    | 5 => !![109, 39, 55, 127; 39, 161, 127, 10; 55, 127, 109, 39; 127, 10, 39, 161]
    | 6 => !![129, -47, 37, 39; -47, 129, 39, 37; 37, 39, 129, -54; 39, 37, -54, 129]
    | _ => !![106, -62, 107, -48; -62, 155, -54, 159; 107, -54, 114, -40; -48, 159, -40, 219]
private def blockB (p : Fin 2) (h : Fin 8) : Matrix (Fin 4) (Fin 4) ℂ :=
  match p.val with
  | 0 => match h.val with
    | 0 => !![125, 127, 127, 125; 127, 129, 129, 127; 127, 129, 129, 127; 125, 127, 127, 125]
    | 1 => !![55, 39, -69, -50; 39, 10, -50, -14; -69, -50, 55, 39; -50, -14, 39, 10]
    | 2 => !![30, 121, -51, 39; 121, 30, 39, -51; -51, 39, 45, 133; 39, -51, 133, 45]
    | 3 => !![-73, 50, 107, 35; 50, -37, 37, 159; 107, 37, -63, 28; 35, 159, 28, -29]
    | 4 => !![-48, 37, 39, 125; 37, -54, 129, 39; 39, 129, -54, 37; 125, 39, 37, -48]
    | 5 => !![53, -51, 53, -51; -51, 9, -51, 9; 53, -51, 53, -51; -51, 9, -51, 9]
    | 6 => !![35, 30, 37, 38; 30, 35, 38, 37; 37, 38, 43, 45; 38, 37, 45, 43]
    | _ => !![103, -47, 56, 41; -47, 152, 34, 9; 56, 34, 98, -55; 41, 9, -55, 145]
  | _ => match h.val with
    | 0 => !![-48, -51, 37, 41; -51, -54, 34, 37; 37, 34, -54, -51; 41, 37, -51, -48]
    | 1 => !![53, 37, 56, 38; 37, 9, 38, 9; 56, 38, 53, 37; 38, 9, 37, 9]
    | 2 => !![35, -47, 39, -51; -47, 35, -51, 39; 39, -51, 43, -55; -51, 39, -55, 43]
    | 3 => !![103, 30, 53, 125; 30, 152, 129, 9; 53, 129, 98, 45; 125, 9, 45, 145]
    | 4 => !![125, 39, -51, 35; 39, 129, 37, -51; -51, 37, 129, 39; 35, -51, 39, 125]
    | 5 => !![55, 127, 107, 39; 127, 10, 39, 159; 107, 39, 55, 127; 39, 159, 127, 10]
    | 6 => !![30, 50, 127, -50; 50, 30, -50, 127; 127, -50, 45, 28; -50, 127, 28, 45]
    | _ => !![-73, 121, -69, 125; 121, -37, 129, -14; -69, 129, -63, 133; 125, -14, 133, -29]
private def certIndex (p : Fin 2) (h : Fin 8) (e : Fin 2) : Fin 32 :=
  ⟨p.val * 16 + h.val * 2 + e.val, by omega⟩
private def blockC (p : Fin 2) (h : Fin 8) (e : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  blockA p h + (if e = 0 then (1 : ℂ) else -1) • blockB p h
private def lower (t : Fin 32) : Matrix (Fin 4) (Fin 4) ℂ :=
  match t.val with
    | 0 => !![1, 0, 0, 0; (127/126), 1, 0, 0; (127/126), (125/251), 1, 0; (125/126), (127/251), (127/376), 1]
    | 1 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
    | 2 => !![1, 0, 0, 0; (83/329), 1, 0, 0; (-15/658), (-3032/1027), 1, 0; (-13/658), (-566/1027), (329923/1294945), 1]
    | 3 => !![1, 0, 0, 0; (22/137), 1, 0, 0; (123/548), (9213/1489), 1, 0; (87/548), (1237/1489), (75079/621227), 1]
    | 4 => !![1, 0, 0, 0; (151/153), 1, 0, 0; (-4/51), (-3/76), 1, 0; (-4/51), (-3/76), (1682/1701), 1]
    | 5 => !![1, 0, 0, 0; (-91/93), 1, 0, 0; (30/31), (-45/92), 1, 0; (-30/31), (45/92), (1/45), 1]
    | 6 => !![1, 0, 0, 0; (89/45), 1, 0, 0; (13/15), (84/629), 1, 0; (71/45), (161/629), (1251/2485), 1]
    | 7 => !![1, 0, 0, 0; (-11/191), 1, 0, 0; (-175/191), (-970/50303), 1, 0; (1/191), (-33223/50303), (279789/179167), 1]
    | 8 => !![1, 0, 0, 0; (76/79), 1, 0, 0; (76/79), (149/307), 1, 0; (77/79), (152/307), (1/3), 1]
    | 9 => !![1, 0, 0, 0; (2/175), 1, 0, 0; (-2/175), (-32021/32371), 1, 0; (-173/175), (-4/32371), (1/16098), 1]
    | 10 => !![1, 0, 0, 0; (-2/27), 1, 0, 0; (80/81), (-2/2283), 1, 0; (-2/27), (752/761), (-6/13613), 1]
    | 11 => !![1, 0, 0, 0; (45/28), 1, 0, 0; (27/28), (45/103), 1, 0; (45/28), (75/103), (9/26), 1]
    | 12 => !![1, 0, 0, 0; (-8/41), 1, 0, 0; (-7/82), (6653/6468), 1, 0; (165/164), (373/3234), (2392/25195), 1]
    | 13 => !![1, 0, 0, 0; (-46/47), 1, 0, 0; (-44/47), (45/62), 1, 0; (89/94), (-7/31), (-64/95), 1]
    | 14 => !![1, 0, 0, 0; (-94/209), 1, 0, 0; (111/209), (25273/55327), 1, 0; (4/11), (11115/55327), (-4803953/2705790), 1]
    | 15 => !![1, 0, 0, 0; 0, 1, 0, 0; (-1/3), 1, 1, 0; -2, (1/3), (-3/19), 1]
    | 16 => !![1, 0, 0, 0; (76/79), 1, 0, 0; (76/79), (228/307), 1, 0; (77/79), (152/307), (152/535), 1]
    | 17 => !![1, 0, 0, 0; (178/175), 1, 0, 0; (2/175), (1044/691), 1, 0; (-1/35), (1240/691), (115640/121591), 1]
    | 18 => !![1, 0, 0, 0; (1/4), 1, 0, 0; (-3/164), (-10/3), 1, 0; (-13/656), (-11/12), (76061/306244), 1]
    | 19 => !![1, 0, 0, 0; (9/55), 1, 0, 0; (-62/275), (-3779/620), 1, 0; (-89/550), (-519/620), (38497/320077), 1]
    | 20 => !![1, 0, 0, 0; (-4/79), 1, 0, 0; (83/79), (-221/6225), 1, 0; (-7/79), (6529/6225), (9817/21142), 1]
    | 21 => !![1, 0, 0, 0; (43/44), 1, 0, 0; 1, (44/87), 1, 0; 1, (44/87), (173/260), 1]
    | 22 => !![1, 0, 0, 0; (60/221), 1, 0, 0; (107/221), (50598/80159), 1, 0; (250/221), (-11022/80159), (17648/107273), 1]
    | 23 => !![1, 0, 0, 0; 0, 1, 0, 0; (1/15), 0, 1, 0; 0, 0, 0, 1]
    | 24 => !![1, 0, 0, 0; (13/42), 1, 0, 0; (-17/42), (739/1651), 1, 0; (5/18), (-2597/4953), (44491/47180), 1]
    | 25 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
    | 26 => !![1, 0, 0, 0; (83/82), 1, 0, 0; (81/82), (83/122), 1, 0; (83/82), (20/61), (166/317), 1]
    | 27 => !![1, 0, 0, 0; (-44/27), 1, 0, 0; (-26/27), (88/205), 1, 0; (44/27), (-151/205), (-88/259), 1]
    | 28 => !![1, 0, 0, 0; (1/53), 1, 0, 0; (164/159), (-83/936), 1, 0; (-11/159), (967/936), (-29/1121), 1]
    | 29 => !![1, 0, 0, 0; (-97/99), 1, 0, 0; (-10/11), (81/392), 1, 0; (89/99), (-277/392), (-67/263), 1]
    | 30 => !![1, 0, 0, 0; (59/33), 1, 0, 0; (38/33), (233/413), 1, 0; (7/3), (242/413), (81/1346), 1]
    | _ => !![1, 0, 0, 0; (-183/179), 1, 0, 0; (176/179), (-183/293), 1, 0; (-173/179), (-692/879), (-1557/596), 1]
private def pivots (t : Fin 32) : Fin 4 → ℂ :=
  match t.val with
    | 0 => ![252, (251/63), (752/251), (493/188)]
    | 1 => ![2, 2, 2, 2]
    | 2 => ![658, (1027/329), (1294945/2054), (3718399/1294945)]
    | 3 => ![548, (1489/137), (621227/5956), (1343967/621227)]
    | 4 => ![153, (608/153), (3402/19), (6766/1701)]
    | 5 => ![93, (368/93), (45/23), (88/45)]
    | 6 => ![45, (629/45), (2485/629), (10091/2485)]
    | 7 => ![191, (50303/191), (179167/50303), (9393257/179167)]
    | 8 => ![79, (307/79), (912/307), (8/3)]
    | 9 => ![175, (32371/175), (128784/32371), (32012/8049)]
    | 10 => ![162, (1522/9), (27226/6849), (54130/13613)]
    | 11 => ![56, (103/14), (260/103), (41/13)]
    | 12 => ![164, (6468/41), (25195/6468), (389033/100780)]
    | 13 => ![94, (186/47), (95/62), (159/190)]
    | 14 => ![209, (55327/209), (5411580/55327), (23490908/1352895)]
    | 15 => ![3, 3, (38/3), (3497/57)]
    | 16 => ![79, (307/79), (535/307), (1528/535)]
    | 17 => ![175, (691/175), (121591/691), (362440/121591)]
    | 18 => ![656, 3, (76561/123), (3460641/1224976)]
    | 19 => ![550, (124/11), (320077/3100), (1411809/640154)]
    | 20 => ![158, (12450/79), (21142/6225), (56323/21142)]
    | 21 => ![88, (87/22), (260/87), (433/260)]
    | 22 => ![221, (80159/221), (214546/80159), (242916/107273)]
    | 23 => ![15, 75, (44/15), 2]
    | 24 => ![252, (1651/7), (283080/1651), (3235903/212310)]
    | 25 => ![2, 2, 2, 2]
    | 26 => ![164, (122/41), (317/122), (616/317)]
    | 27 => ![54, (205/27), (518/205), (824/259)]
    | 28 => ![159, (8424/53), (1121/312), (4025/1121)]
    | 29 => ![99, (392/99), (789/392), (495/263)]
    | 30 => ![33, (413/33), (1346/413), (8109/1346)]
    | _ => ![179, (879/179), (596/293), (114205/1788)]

private theorem ldl_0 :
    blockC 0 0 0 = lower 0 * diagonal (pivots 0) * (lower 0)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_1 :
    blockC 0 0 1 = lower 1 * diagonal (pivots 1) * (lower 1)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_2 :
    blockC 0 1 0 = lower 2 * diagonal (pivots 2) * (lower 2)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_3 :
    blockC 0 1 1 = lower 3 * diagonal (pivots 3) * (lower 3)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_4 :
    blockC 0 2 0 = lower 4 * diagonal (pivots 4) * (lower 4)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_5 :
    blockC 0 2 1 = lower 5 * diagonal (pivots 5) * (lower 5)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_6 :
    blockC 0 3 0 = lower 6 * diagonal (pivots 6) * (lower 6)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_7 :
    blockC 0 3 1 = lower 7 * diagonal (pivots 7) * (lower 7)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_8 :
    blockC 0 4 0 = lower 8 * diagonal (pivots 8) * (lower 8)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_9 :
    blockC 0 4 1 = lower 9 * diagonal (pivots 9) * (lower 9)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_10 :
    blockC 0 5 0 = lower 10 * diagonal (pivots 10) * (lower 10)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_11 :
    blockC 0 5 1 = lower 11 * diagonal (pivots 11) * (lower 11)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_12 :
    blockC 0 6 0 = lower 12 * diagonal (pivots 12) * (lower 12)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_13 :
    blockC 0 6 1 = lower 13 * diagonal (pivots 13) * (lower 13)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_14 :
    blockC 0 7 0 = lower 14 * diagonal (pivots 14) * (lower 14)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_15 :
    blockC 0 7 1 = lower 15 * diagonal (pivots 15) * (lower 15)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_16 :
    blockC 1 0 0 = lower 16 * diagonal (pivots 16) * (lower 16)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_17 :
    blockC 1 0 1 = lower 17 * diagonal (pivots 17) * (lower 17)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_18 :
    blockC 1 1 0 = lower 18 * diagonal (pivots 18) * (lower 18)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_19 :
    blockC 1 1 1 = lower 19 * diagonal (pivots 19) * (lower 19)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_20 :
    blockC 1 2 0 = lower 20 * diagonal (pivots 20) * (lower 20)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_21 :
    blockC 1 2 1 = lower 21 * diagonal (pivots 21) * (lower 21)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_22 :
    blockC 1 3 0 = lower 22 * diagonal (pivots 22) * (lower 22)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_23 :
    blockC 1 3 1 = lower 23 * diagonal (pivots 23) * (lower 23)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_24 :
    blockC 1 4 0 = lower 24 * diagonal (pivots 24) * (lower 24)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_25 :
    blockC 1 4 1 = lower 25 * diagonal (pivots 25) * (lower 25)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_26 :
    blockC 1 5 0 = lower 26 * diagonal (pivots 26) * (lower 26)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_27 :
    blockC 1 5 1 = lower 27 * diagonal (pivots 27) * (lower 27)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_28 :
    blockC 1 6 0 = lower 28 * diagonal (pivots 28) * (lower 28)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_29 :
    blockC 1 6 1 = lower 29 * diagonal (pivots 29) * (lower 29)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_30 :
    blockC 1 7 0 = lower 30 * diagonal (pivots 30) * (lower 30)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_31 :
    blockC 1 7 1 = lower 31 * diagonal (pivots 31) * (lower 31)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, blockC, blockA, blockB, lower, pivots, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_four, map_ofNat]
private theorem ldl_certificate (p : Fin 2) (h : Fin 8) (e : Fin 2) :
    blockC p h e = lower (certIndex p h e) * diagonal (pivots (certIndex p h e)) *
      (lower (certIndex p h e))ᴴ := by
  fin_cases p <;> fin_cases h <;> fin_cases e
  · exact ldl_0
  · exact ldl_1
  · exact ldl_2
  · exact ldl_3
  · exact ldl_4
  · exact ldl_5
  · exact ldl_6
  · exact ldl_7
  · exact ldl_8
  · exact ldl_9
  · exact ldl_10
  · exact ldl_11
  · exact ldl_12
  · exact ldl_13
  · exact ldl_14
  · exact ldl_15
  · exact ldl_16
  · exact ldl_17
  · exact ldl_18
  · exact ldl_19
  · exact ldl_20
  · exact ldl_21
  · exact ldl_22
  · exact ldl_23
  · exact ldl_24
  · exact ldl_25
  · exact ldl_26
  · exact ldl_27
  · exact ldl_28
  · exact ldl_29
  · exact ldl_30
  · exact ldl_31
private theorem pivots_positive (t : Fin 32) (i : Fin 4) : 0 < pivots t i := by
  fin_cases t <;> fin_cases i <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, pivots]
private theorem blockC_psd (p : Fin 2) (h : Fin 8) (e : Fin 2) :
    (blockC p h e).PosSemidef := by
  rw [ldl_certificate]
  exact (Matrix.PosDef.diagonal (pivots_positive _)).posSemidef.mul_mul_conjTranspose_same _

private def sector (p : Fin 2) (h : Fin 8) : Matrix (Fin 8) (Fin 8) ℂ :=
  fun x y => if (x.val < 4) = (y.val < 4) then blockA p h ((Fin.ofNat 4 x.val)) ((Fin.ofNat 4 y.val))
    else blockB p h ((Fin.ofNat 4 x.val)) ((Fin.ofNat 4 y.val))
private def embedding (e : Fin 2) : Matrix (Fin 8) (Fin 4) ℂ :=
  fun x i => if (Fin.ofNat 4 x.val) = i then (if e = 0 ∨ x.val < 4 then 1 else -1) else 0

private def rawState (p : Fin 2) : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ :=
  (Matrix.blockDiagonal' (sector p)).submatrix
    (fun ij => ⟨Fin.xor ij.1 ij.2, ij.1⟩) (fun ij => ⟨Fin.xor ij.1 ij.2, ij.1⟩)
private def rho : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ :=
  (1 / 10134 : ℂ) • rawState 0

private theorem xor8_table : (Fin.xor (n := 8)) = (fun x y =>
  match x.val with
  | 0 => match y.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | _ => 7
  | 1 => match y.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | _ => 6
  | 2 => match y.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | _ => 5
  | 3 => match y.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 7 | 5 => 6 | 6 => 5 | _ => 4
  | 4 => match y.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7 | 4 => 0 | 5 => 1 | 6 => 2 | _ => 3
  | 5 => match y.val with | 0 => 5 | 1 => 4 | 2 => 7 | 3 => 6 | 4 => 1 | 5 => 0 | 6 => 3 | _ => 2
  | 6 => match y.val with | 0 => 6 | 1 => 7 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3 | 6 => 0 | _ => 1
  | _ => match y.val with | 0 => 7 | 1 => 6 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2 | 6 => 1 | _ => 0
) := by
  ext x y
  revert x y
  decide

private theorem embedding_mul (e : Fin 2) (C : Matrix (Fin 4) (Fin 4) ℂ)
    (x y : Fin 8) :
    (embedding e * C * (embedding e)ᴴ) x y =
      (if e = 0 ∨ x.val < 4 then 1 else -1) * C ((Fin.ofNat 4 x.val)) ((Fin.ofNat 4 y.val)) *
        (if e = 0 ∨ y.val < 4 then 1 else -1) := by
  by_cases hx : e = 0 ∨ x.val < 4 <;> by_cases hy : e = 0 ∨ y.val < 4
  all_goals simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedding,
    ite_mul, mul_ite, hx, hy, apply_ite]
private theorem sector_decomposition (p : Fin 2) (h : Fin 8) :
    sector p h = (1/2 : ℂ) •
      (embedding 0 * blockC p h 0 * (embedding 0)ᴴ +
       embedding 1 * blockC p h 1 * (embedding 1)ᴴ) := by
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, embedding_mul]
  by_cases hx : x.val < 4 <;> by_cases hy : y.val < 4
  all_goals norm_num [sector, blockC, hx, hy]
  all_goals ring

private theorem rawState_apply (p : Fin 2) (x z y w : Fin 8) :
    rawState p (x,z) (y,w) =
      if Fin.xor x z = Fin.xor y w then sector p (Fin.xor x z) x y else 0 := by
  simp [rawState, Matrix.blockDiagonal', Matrix.submatrix]

private theorem xor_cancel (x h : Fin 8) : Fin.xor x (Fin.xor x h) = h := by
  exact xor_cancel_left (α := Fin (2 ^ 3)) x h
private theorem xor_relation (x z y w : Fin 8) :
    Fin.xor x w = Fin.xor y z ↔ Fin.xor x z = Fin.xor y w := by
  rw [← xor_zero (Fin.xor x w) (Fin.xor y z), ← xor_zero (Fin.xor x z) (Fin.xor y w)]
  have he : Fin.xor (Fin.xor x w) (Fin.xor y z) =
      Fin.xor (Fin.xor x z) (Fin.xor y w) := by
    change (x ^^^ w) ^^^ (y ^^^ z) = (x ^^^ z) ^^^ (y ^^^ w)
    simp only [Fin.xor_assoc (n := 3) rfl]
    congr 1
    rw [Fin.xor_comm w (y ^^^ z), Fin.xor_assoc (n := 3) rfl,
      ← Fin.xor_assoc (n := 3) rfl y z w, Fin.xor_comm y z, Fin.xor_assoc (n := 3) rfl]
  rw [he]
private theorem sector_pt (h x y : Fin 8) :
    sector 0 (Fin.xor x (Fin.xor y h)) x y = sector 1 h x y := by
  fin_cases h <;> fin_cases x <;> fin_cases y
  all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq, Fin.reduceLE, Fin.reduceLT, Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.sum_univ_succ, sector, blockA, blockB, Fin.ofNat, xor8_table, Matrix.vecHead, Matrix.vecTail, Matrix.vecHead, Matrix.vecTail]

private theorem xor_nested (x y z : Fin 8) :
    Fin.xor x (Fin.xor y (Fin.xor x z)) = Fin.xor y z := by
  change x ^^^ (y ^^^ (x ^^^ z)) = y ^^^ z
  rw [← Fin.xor_assoc (n := 3) rfl x y (x ^^^ z), Fin.xor_comm x y,
    Fin.xor_assoc (n := 3) rfl]
  have hc := xor_cancel x z
  change x ^^^ (x ^^^ z) = z at hc
  rw [hc]
private theorem rawState_pt : partialTransposeB (rawState 0) = rawState 1 := by
  ext ⟨x,z⟩ ⟨y,w⟩
  simp only [partialTransposeB, rawState_apply]
  by_cases he : Fin.xor x z = Fin.xor y w
  · have hr := (xor_relation x z y w).2 he
    simp only [he, hr, if_true]
    have hh := xor_nested x y z
    rw [← hh, sector_pt, he]

  · simp only [he, (xor_relation x z y w).not.mpr he, if_false]

private theorem sector_psd (p : Fin 2) (h : Fin 8) : (sector p h).PosSemidef := by
  rw [sector_decomposition]
  apply Matrix.PosSemidef.smul _ (by norm_num [Complex.le_def])
  exact ((blockC_psd p h 0).mul_mul_conjTranspose_same _).add
    ((blockC_psd p h 1).mul_mul_conjTranspose_same _)
private theorem rawState_psd (p : Fin 2) : (rawState p).PosSemidef := by
  exact (posSemidef_blockDiagonal (sector p) (sector_psd p)).submatrix _
private theorem rho_psd : rho.PosSemidef :=
  (rawState_psd 0).smul (by norm_num [Complex.le_def])
private theorem rho_ppt : (partialTransposeB rho).PosSemidef := by
  have he : partialTransposeB rho = (1/10134 : ℂ) • rawState 1 := by
    rw [← rawState_pt]
    rfl
  rw [he]
  exact (rawState_psd 1).smul (by norm_num [Complex.le_def])

private theorem walsh_sym (x k : Fin 8) : walsh x k = walsh k x := by
  revert x k
  decide
private theorem xor_cross (x y z w : Fin 8) :
    Fin.xor x y = Fin.xor z w ↔ Fin.xor x z = Fin.xor y w := by
  have hr := xor_relation x z w y
  change x ^^^ y = w ^^^ z ↔ x ^^^ z = w ^^^ y at hr
  change x ^^^ y = z ^^^ w ↔ x ^^^ z = y ^^^ w
  simpa only [Fin.xor_comm w z, Fin.xor_comm w y] using hr
private theorem walsh_four_sum (x y z w : Fin 8) :
    (∑ k : Fin 8, (walsh x k : ℂ) * (walsh y k : ℂ) *
      (walsh z k : ℂ) * (walsh w k : ℂ)) =
      if Fin.xor x z = Fin.xor y w then 8 else 0 := by
  have he : (∑ k : Fin 8, (walsh x k : ℂ) * (walsh y k : ℂ) *
      (walsh z k : ℂ) * (walsh w k : ℂ)) =
      gram 0 0 (Fin.xor (Fin.xor x y) (Fin.xor z w)) := by
    unfold gram
    apply Finset.sum_congr rfl
    intro k _
    simp only [phase, Matrix.cons_val_zero, star_one, one_mul]
    rw [walsh_sym x k, walsh_sym y k, walsh_sym z k, walsh_sym w k]
    have h1 := walsh_product k x y
    have h2 := walsh_product k z w
    have h3 := walsh_product k (Fin.xor x y) (Fin.xor z w)
    push_cast [← h1, ← h2, ← h3]
    ring
  rw [he, gram_same]
  simp only [xor_zero, xor_cross]

private theorem columnProjector_scaled (α : Fin 3) (i x y : Fin 8) :
    (Matrix.vecMulVec (fun x => scaledBasis α x i) (star (fun x => scaledBasis α x i))) x y =
      (1/8 : ℂ) * phase α x * star (phase α y) *
        (walsh x i : ℂ) * (walsh y i : ℂ) := by
  simp only [Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply, scaledBasis,
    star_mul, Complex.star_def, Complex.conj_ofReal, map_intCast]
  calc
    _ = (((Real.sqrt 8)⁻¹ : ℝ) : ℂ)^2 * phase α x * (starRingEnd ℂ) (phase α y) *
      (walsh x i : ℂ) * (walsh y i : ℂ) := by ring
    _ = _ := by rw [scale_complex_sq]

private def correlator (α : Fin 3) : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ :=
  ∑ i : Fin 8, Matrix.kronecker ((Matrix.vecMulVec (fun x => scaledBasis α x i) (star (fun x => scaledBasis α x i))))
    (((Matrix.vecMulVec (fun x => scaledBasis α x i) (star (fun x => scaledBasis α x i)))).map (star : ℂ → ℂ))

private theorem correlator_apply (α : Fin 3) (x z y w : Fin 8) :
    correlator α (x,z) (y,w) =
      if Fin.xor x z = Fin.xor y w then
        (1/8 : ℂ) * phase α x * star (phase α y) *
          star (phase α z) * phase α w else 0 := by
  change (∑ i : Fin 8, (Matrix.vecMulVec (fun x => scaledBasis α x i) (star (fun x => scaledBasis α x i))) x y *
    star ((Matrix.vecMulVec (fun x => scaledBasis α x i) (star (fun x => scaledBasis α x i))) z w)) = _
  simp only [columnProjector_scaled, star_mul, star_star,
    Complex.star_def, map_div₀, map_one, map_ofNat, map_intCast]
  have hf := walsh_four_sum x y z w
  calc
    _ = ((1/64 : ℂ) * phase α x * star (phase α y) *
      star (phase α z) * phase α w) *
      (∑ i : Fin 8, (walsh x i : ℂ) * (walsh y i : ℂ) *
        (walsh z i : ℂ) * (walsh w i : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      norm_num [Complex.star_def]
      ring
    _ = _ := by rw [hf]; split_ifs <;> simp only [Complex.star_def] <;> ring

private theorem xor_eq_iff (x y h : Fin 8) : Fin.xor x y = h ↔ y = Fin.xor x h := by
  exact xor_eq_iff_right_eq (α := Fin (2 ^ 3)) x y h
private theorem rawState_trace_formula (p : Fin 2) :
    Matrix.trace (rawState p) = ∑ h : Fin 8, ∑ x : Fin 8, sector p h x x := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, rawState_apply, ite_true]
  calc
    _ = ∑ x : Fin 8, ∑ h : Fin 8, sector p h x x := by
      apply Finset.sum_congr rfl
      intro x _
      exact Equiv.sum_comp (Function.Involutive.toPerm (Fin.xor x) (xor_cancel x)) (fun h => sector p h x x)
    _ = _ := Finset.sum_comm
private theorem rawState_trace : Matrix.trace (rawState 0) = 10134 := by
  rw [rawState_trace_formula]
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sector, blockA, Fin.ofNat, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk]

private theorem trace_sector (W : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ) :
    Matrix.trace (W * rawState 0) =
      ∑ h : Fin 8, ∑ x : Fin 8, ∑ y : Fin 8,
        W (x, Fin.xor x h) (y, Fin.xor y h) * sector 0 h y x := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    rawState_apply]
  have hc (x z y : Fin 8) :
      (∑ w : Fin 8, W (x,z) (y,w) *
        (if Fin.xor y w = Fin.xor x z then sector 0 (Fin.xor y w) y x else 0)) =
        W (x,z) (y, Fin.xor y (Fin.xor x z)) * sector 0 (Fin.xor x z) y x := by
    rw [Finset.sum_eq_single (Fin.xor y (Fin.xor x z))]
    · simp only [xor_cancel, ite_true]
    · intro w _ hw
      rw [if_neg ((xor_eq_iff y w (Fin.xor x z)).not.mpr hw), mul_zero]
    · simp
  simp_rw [hc]
  calc
    _ = ∑ x : Fin 8, ∑ h : Fin 8, ∑ y : Fin 8,
        W (x, Fin.xor x h) (y, Fin.xor y h) * sector 0 h y x := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Function.Involutive.toPerm, Equiv.coe_fn_mk, xor_cancel] using
        Equiv.sum_comp (Function.Involutive.toPerm (Fin.xor x) (xor_cancel x)) (fun h => ∑ y : Fin 8,
          W (x, Fin.xor x h) (y, Fin.xor y h) * sector 0 h y x)
    _ = _ := Finset.sum_comm

private def sectorReading (α : Fin 3) (h : Fin 8) : ℂ :=
  ∑ x : Fin 8, ∑ y : Fin 8,
    (1/8 : ℂ) * phase α x * star (phase α y) *
      star (phase α (Fin.xor x h)) * phase α (Fin.xor y h) * sector 0 h y x
private theorem correlator_trace_formula (α : Fin 3) :
    Matrix.trace (correlator α * rawState 0) = ∑ h : Fin 8, sectorReading α h := by
  rw [trace_sector]
  simp only [correlator_apply, xor_cancel, ite_true, sectorReading]

private theorem phase_table : phase = (fun α x =>
  match α.val with
  | 0 => 1
  | 1 => match x.val with
    | 0 => 1 | 1 => 1 | 2 => Complex.I | 3 => Complex.I
    | 4 => Complex.I | 5 => -Complex.I | 6 => -1 | _ => 1
  | _ => match x.val with
    | 0 => 1 | 1 => 1 | 2 => 1 | 3 => -1
    | 4 => Complex.I | 5 => Complex.I | 6 => -Complex.I | _ => Complex.I) := by
  funext α x
  fin_cases α <;> fin_cases x <;> norm_num [phase]
private theorem reading_0 : sectorReading 0 0 = (1018 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_1 : sectorReading 0 1 = (989/2 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_2 : sectorReading 0 2 = (307 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_3 : sectorReading 0 3 = (1363/4 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_4 : sectorReading 0 4 = (306 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_5 : sectorReading 0 5 = (306 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_6 : sectorReading 0 6 = (611/2 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_7 : sectorReading 0 7 = (310 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_8 : sectorReading 1 0 = (1018 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_9 : sectorReading 1 1 = (1069/2 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_10 : sectorReading 1 2 = (355 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_11 : sectorReading 1 3 = (1475/4 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_12 : sectorReading 1 4 = (354 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_13 : sectorReading 1 5 = (354 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_14 : sectorReading 1 6 = (711/2 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_15 : sectorReading 1 7 = (383 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_16 : sectorReading 2 0 = (1018 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_17 : sectorReading 2 1 = (1081/2 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_18 : sectorReading 2 2 = (361 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_19 : sectorReading 2 3 = (1511/4 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_20 : sectorReading 2 4 = (362 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_21 : sectorReading 2 5 = (386 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_22 : sectorReading 2 6 = (721/2 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private theorem reading_23 : sectorReading 2 7 = (366 : ℂ) := by
  apply Complex.ext <;>
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sectorReading, sector, blockA, blockB, Fin.ofNat, xor8_table, phase_table, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceLT, Fin.reduceLE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
private def readingValue : Fin 3 → Fin 8 → ℂ :=
  ![![1018,989/2,307,1363/4,306,306,611/2,310],
    ![1018,1069/2,355,1475/4,354,354,711/2,383],
    ![1018,1081/2,361,1511/4,362,386,721/2,366]]
private theorem sectorReading_exact (α : Fin 3) (h : Fin 8) :
    sectorReading α h = readingValue α h := by
  fin_cases α <;> fin_cases h
  all_goals norm_num [readingValue, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  · exact reading_0
  · exact reading_1
  · exact reading_2
  · exact reading_3
  · exact reading_4
  · exact reading_5
  · exact reading_6
  · exact reading_7
  · exact reading_8
  · exact reading_9
  · exact reading_10
  · exact reading_11
  · exact reading_12
  · exact reading_13
  · exact reading_14
  · exact reading_15
  · exact reading_16
  · exact reading_17
  · exact reading_18
  · exact reading_19
  · exact reading_20
  · exact reading_21
  · exact reading_22
  · exact reading_23

private def shifted : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ :=
  ∑ l : Fin 8, Matrix.single (l,l+1) (l,l+1) (1 : ℂ)
private theorem witness_decomposition : witnessGamma fourBases 1 =
    (11/8 : ℂ) • 1 - shifted - ∑ α : Fin 3, correlator α := by
  norm_num [witnessGamma, fourBases, Finset.sum_filter, Fin.sum_univ_succ, correlator, shifted, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk]

private theorem rho_density : IsDensity rho := by
  refine ⟨rho_psd, ?_⟩
  norm_num [rho, Matrix.trace_smul, smul_eq_mul, rawState_trace]
private theorem shifted_trace : Matrix.trace (shifted * rawState 0) = 3304 := by
  simp only [shifted, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul,
    one_smul, rawState_apply, ite_true]
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, sector, blockA, Fin.ofNat, xor8_table, Fin.add_def, Fin.reduceAdd, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk]
private theorem correlator_trace_exact (α : Fin 3) :
    Matrix.trace (correlator α * rawState 0) =
      ![(13551/4 : ℂ),14891/4,15087/4] α := by
  rw [correlator_trace_formula]
  simp_rw [sectorReading_exact]
  fin_cases α <;> norm_num [readingValue, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
private theorem witness_raw_trace :
    Matrix.trace (witnessGamma fourBases 1 * rawState 0) = -252 := by
  rw [witness_decomposition]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.sum_mul,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul,
    rawState_trace, shifted_trace, correlator_trace_exact]
  norm_num [Fin.sum_univ_succ]
private theorem witness_trace :
    Matrix.trace (witnessGamma fourBases 1 * rho) = (-14/563 : ℂ) := by
  simp only [rho, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, witness_raw_trace]
  norm_num
/-- Four MUBs detect a PPT state at d=8, refuting the necessity bound. -/
theorem result : ¬ claim := by
  intro hc
  have hd : DetectsBoundEntanglement fourBases 1 := by
    refine ⟨rho, rho_density, rho_ppt, ?_⟩
    rw [witness_trace]
    norm_num
  exact (hc 3 (by decide) 4 (by decide) fourBases fourBases_mub 1) hd

end
end D5.S3.Quantum.Entanglement.FourMUBBoundEntanglementRefutation
