/- GID: D5/S3/Geometry/Lorentz/WeylNullScreen
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/WeylNullScreen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: 4D Lorentzian algebraic curvature decomposition and sharp five-null-ray Weyl tidal reconstruction. -/

import OmegaBuild.Commands
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Data.Matrix.Block
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.WeylNullScreen

open Matrix Polynomial Module

/-- The oriented bivector basis (01, 02, 03, 23, 31, 12). -/
abbrev PairIndex := Fin 3 ⊕ Fin 3
private noncomputable def symmetricKernel {K ι : Type*} [Field K] (tr : Matrix ι ι K →ₗ[K] K) :
    Submodule K (Matrix ι ι K) where
  carrier := {C | (∀ i j, C i j = C j i) ∧ tr C = 0}
  zero_mem' := ⟨fun _ _ => rfl, tr.map_zero⟩
  add_mem' {C D} h₁ h₂ := ⟨fun i j => by
    change C i j + D i j = C j i + D j i
    rw [h₁.1 i j, h₂.1 i j], by rw [map_add, h₁.2, h₂.2, add_zero]⟩
  smul_mem' a C h := ⟨fun i j => by change a * _ = a * _; rw [h.1 i j],
    by rw [map_smul, h.2, smul_zero]⟩
private noncomputable def diagSum {K ι : Type*} [Field K] [Fintype ι] (w : ι → K) :
    Matrix ι ι K →ₗ[K] K where
  toFun C := ∑ i, w i * C i i
  map_add' C D := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a C := by simp [Finset.mul_sum, mul_left_comm]
private noncomputable def bianchi : Matrix PairIndex PairIndex ℝ →ₗ[ℝ] ℝ where
  toFun C := trace (fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℝ) 1 1 0 * C)
  map_add' _ _ := by simp [Matrix.mul_add]
  map_smul' _ _ := by simp
/-- Symmetric pair matrices with the algebraic Bianchi trace zero. -/
abbrev AlgebraicCurvature4 := symmetricKernel bianchi

private theorem bianchi_apply (C : Matrix PairIndex PairIndex ℝ) :
    bianchi C = (∑ i : Fin 3, C (.inr i) (.inl i)) + ∑ i : Fin 3, C (.inl i) (.inr i) := by
  change trace (fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℝ) 1 1 0 * C) = _
  conv_lhs => rw [← fromBlocks_toBlocks C, fromBlocks_multiply]
  simp [trace, Fintype.sum_sum_type, toBlocks₁₂, toBlocks₂₁]
/-- Symmetric traceless spatial matrices over the indicated field. -/
abbrev STF3 (K : Type*) [Field K] := symmetricKernel (diagSum (fun _ : Fin 3 => (1 : K)))
private noncomputable def lorentzTrace := diagSum (![(-1 : ℝ), 1, 1, 1] : Fin 4 → ℝ)

/-- Symmetric Ricci forms with Lorentzian trace zero. -/
abbrev TracelessRicci4 := symmetricKernel lorentzTrace
private noncomputable def eta : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![-1, 1, 1, 1]
private noncomputable def pairLeft : PairIndex → Fin 4
  | .inl _ => 0
  | .inr i => ![2, 3, 1] i
private noncomputable def pairRight : PairIndex → Fin 4
  | .inl i => i.succ
  | .inr i => ![3, 1, 2] i
private noncomputable def electric {K : Type*} (C : Matrix PairIndex PairIndex K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => C (.inl i) (.inl j)
private noncomputable def magnetic {K : Type*} (C : Matrix PairIndex PairIndex K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => C (.inl i) (.inr j)
private noncomputable def spatial (C : Matrix PairIndex PairIndex ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => C (.inr i) (.inr j)
private noncomputable def contractions (C : Matrix PairIndex PairIndex ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let E := electric C
  let M := magnetic C
  let S := spatial C
  let t := E 0 0 + E 1 1 + E 2 2
  let x := M 1 2 - M 2 1
  let y := M 2 0 - M 0 2
  let z := M 0 1 - M 1 0
  !![t, x, y, z;
      x, -E 0 0 + S 1 1 + S 2 2, -E 0 1 - S 0 1, -E 0 2 - S 0 2;
      y, -E 0 1 - S 0 1, -E 1 1 + S 0 0 + S 2 2, -E 1 2 - S 1 2;
      z, -E 0 2 - S 0 2, -E 1 2 - S 1 2, -E 2 2 + S 0 0 + S 1 1]

/-- The contraction Ric_bd = η^ac R_abcd in the oriented pair basis. -/
noncomputable def ricci : AlgebraicCurvature4 →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun C := contractions C.val
  map_add' _ _ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [contractions, electric, magnetic, spatial] <;> ring
  map_smul' _ _ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [contractions, electric, magnetic, spatial] <;> ring
private theorem ricci_symm (C : AlgebraicCurvature4) (i j : Fin 4) :
    ricci C i j = ricci C j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Algebraic Weyl curvature, the Ricci kernel inside algebraic curvature. -/
abbrev Weyl4 := LinearMap.ker ricci
private noncomputable def emBlock {K : Type*} [Ring K] (E M : Matrix (Fin 3) (Fin 3) K) :
    Matrix PairIndex PairIndex K := fromBlocks E M M (-E)
private noncomputable def fromEM (E M : STF3 ℝ) : Weyl4 := by
  refine ⟨⟨emBlock E.val M.val, ?_, ?_⟩, LinearMap.mem_ker.mpr ?_⟩
  · rintro (i | i) (j | j) <;> simp [emBlock, E.property.1 i j, M.property.1 i j]
  · have h : (∑ i : Fin 3, M.val i i) = 0 := by simpa [diagSum] using M.property.2
    simp [bianchi_apply, emBlock, h]
  · have h : E.val 0 0 + E.val 1 1 + E.val 2 2 = 0 := by
      simpa [diagSum, Fin.sum_univ_three] using E.property.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ricci, contractions, electric, magnetic, spatial, emBlock, M.property.1] <;>
      linarith
private theorem weyl_blocks (C : Weyl4) :
    let A := C.val.val
    (∀ i j, magnetic A i j = magnetic A j i) ∧ spatial A = -electric A ∧
      (∑ i, electric A i i) = 0 := by
  let A := C.val.val
  have hr := LinearMap.mem_ker.mp C.property
  have h (i j : Fin 4) : contractions A i j = 0 := congrFun (congrFun hr i) j
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, contractions] at h
  obtain ⟨⟨r00, r01, r02, r03⟩, ⟨_, r11, r12, r13⟩,
    ⟨_, _, r22, r23⟩, ⟨_, _, _, r33⟩⟩ := h
  simp at r00 r01 r02 r03 r11 r12 r13 r22 r23 r33
  refine ⟨?_, ?_, by simpa [Fin.sum_univ_three] using r00⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> first | rfl | linarith!
  · have hE (i j : Fin 3) : electric A i j = electric A j i := C.val.property.1 _ _
    have hS (i j : Fin 3) : spatial A i j = spatial A j i := C.val.property.1 _ _
    ext i j
    fin_cases i <;> fin_cases j <;> rw [Matrix.neg_apply] <;>
      first | linarith! | rw [hE, hS]; linarith!
private noncomputable def electricPart (C : Weyl4) : STF3 ℝ :=
  ⟨electric C.val.val, fun i j => C.val.property.1 _ _,
    by simpa [STF3, diagSum] using (weyl_blocks C).2.2⟩
private noncomputable def magneticPart (C : Weyl4) : STF3 ℝ :=
  ⟨magnetic C.val.val, (weyl_blocks C).1,
    by
      have h := C.val.property.2
      rw [bianchi_apply] at h
      simp only [fun i : Fin 3 => C.val.property.1 (.inr i) (.inl i)] at h
      simp [diagSum, magnetic]
      linarith⟩

/-- The Weyl matrix has blocks E, M, M, −E, with E and M symmetric and traceless. -/
noncomputable def weyl_electric_magnetic_equiv : Weyl4 ≃ₗ[ℝ] (STF3 ℝ × STF3 ℝ) where
  toFun C := (electricPart C, magneticPart C)
  invFun v := fromEM v.1 v.2
  left_inv C := by
    refine Subtype.ext (Subtype.ext (Matrix.ext fun i j => ?_))
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact (weyl_blocks C).1 i j |>.trans (C.val.property.1 (.inl j) (.inr i))
    · exact (congrFun (congrFun (weyl_blocks C).2.1 i) j).symm
  right_inv v := by ext <;> rfl
  map_add' _ _ := by ext <;> rfl
  map_smul' _ _ := by ext <;> rfl
private noncomputable def knEntry (h : Matrix (Fin 4) (Fin 4) ℝ) : Matrix PairIndex PairIndex ℝ := fun i j =>
  let a := pairLeft i
  let b := pairRight i
  let c := pairLeft j
  let d := pairRight j
  eta a c * h b d + eta b d * h a c - eta a d * h b c - eta b c * h a d
private theorem eta_symm (i j : Fin 4) : eta i j = eta j i :=
  (congrFun (congrFun (diagonal_transpose (![(-1 : ℝ), 1, 1, 1] : Fin 4 → ℝ)) i) j).symm
private noncomputable def kn (h : Matrix (Fin 4) (Fin 4) ℝ) (hs : ∀ i j, h i j = h j i) :
    AlgebraicCurvature4 :=
  ⟨knEntry h, by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [knEntry]
      rw [eta_symm (pairLeft j) (pairLeft i), eta_symm (pairRight j) (pairRight i),
        eta_symm (pairLeft j) (pairRight i), eta_symm (pairRight j) (pairLeft i),
        hs (pairRight j) (pairRight i), hs (pairLeft j) (pairLeft i),
        hs (pairRight j) (pairLeft i), hs (pairLeft j) (pairRight i)]
      ring
    · change bianchi (knEntry h) = 0
      simp [bianchi_apply, Fin.sum_univ_three, knEntry, pairLeft, pairRight, eta, diagonal_apply]⟩
private theorem ricci_kn (h : Matrix (Fin 4) (Fin 4) ℝ) (hs : ∀ i j, h i j = h j i) :
    ricci (kn h hs) = (2 : ℝ) • h + lorentzTrace h • eta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ricci, contractions, electric, magnetic, spatial, kn, knEntry, pairLeft, pairRight,
      eta, lorentzTrace, diagSum, Fin.sum_univ_succ, hs 1 0, hs 2 0, hs 3 0,
      hs 2 1, hs 3 1, hs 3 2] <;> ring
private theorem trace_eta : lorentzTrace eta = 4 := by
  norm_num [lorentzTrace, diagSum, eta, diagonal_apply, Fin.sum_univ_succ]
private noncomputable def ricciTF (R : AlgebraicCurvature4) : TracelessRicci4 :=
  ⟨ricci R - (lorentzTrace (ricci R) / 4) • eta,
    fun i j => by simp [ricci_symm R i j, eta_symm i j],
    by rw [map_sub, map_smul, trace_eta, smul_eq_mul]; ring⟩
private noncomputable def liftRicci (S : TracelessRicci4) (r : ℝ) : AlgebraicCurvature4 :=
  (1 / 2 : ℝ) • kn S.val S.property.1 + (r / 24) • kn eta eta_symm
private theorem ricci_lift (S : TracelessRicci4) (r : ℝ) :
    ricci (liftRicci S r) = S.val + (r / 4) • eta := by
  ext i j
  simp [liftRicci, ricci_kn, S.property.2, trace_eta, smul_add]
  ring

/-- Explicit Lorentzian Ricci decomposition, with Kulkarni–Nomizu inverse. -/
noncomputable def curvature_ricci_split : AlgebraicCurvature4 ≃ₗ[ℝ] (Weyl4 × TracelessRicci4 × ℝ) :=
  (show (Weyl4 × TracelessRicci4 × ℝ) ≃ₗ[ℝ] AlgebraicCurvature4 from
  { toFun := fun v => v.1.val + liftRicci v.2.1 v.2.2
    invFun := fun R =>
      let r := lorentzTrace (ricci R)
      let S := ricciTF R
      (⟨R - liftRicci S r, LinearMap.mem_ker.mpr (by
        rw [map_sub, ricci_lift]
        exact sub_eq_zero.mpr (sub_add_cancel (ricci R) ((r / 4) • eta)).symm)⟩, S, r)
    right_inv := fun _ => sub_add_cancel _ _
    left_inv := by
      rintro ⟨C, S, r⟩
      have h : ricci (C.val + liftRicci S r) = S.val + (r / 4) • eta := by
        rw [map_add, LinearMap.mem_ker.mp C.property, ricci_lift, zero_add]
      have hr : lorentzTrace (ricci (C.val + liftRicci S r)) = r := by
        rw [h, map_add, S.property.2, zero_add, map_smul, trace_eta, smul_eq_mul]; ring
      have hs : ricciTF (C.val + liftRicci S r) = S :=
        Subtype.ext (show ricci _ - (_ / 4) • eta = _ by rw [hr, h, add_sub_cancel_right])
      refine Prod.ext (Subtype.ext ?_) (Prod.ext hs hr)
      change C.val + liftRicci S r - liftRicci (ricciTF _) (lorentzTrace (ricci _)) = C.val
      rw [hs, hr, add_sub_cancel_right]
    map_add' u v := by
      apply Subtype.ext
      ext i j
      change u.1.val.val i j + v.1.val.val i j +
        ((1/2) * knEntry (u.2.1.val + v.2.1.val) i j +
          (u.2.2 + v.2.2) / 24 * knEntry eta i j) =
        u.1.val.val i j + ((1/2) * knEntry u.2.1.val i j + u.2.2 / 24 * knEntry eta i j) +
          (v.1.val.val i j + ((1/2) * knEntry v.2.1.val i j + v.2.2 / 24 * knEntry eta i j))
      simp only [knEntry, Matrix.add_apply]
      ring
    map_smul' a v := by
      apply Subtype.ext
      ext i j
      change a * v.1.val.val i j +
        ((1/2) * knEntry (a • v.2.1.val) i j + a * v.2.2 / 24 * knEntry eta i j) =
        a * (v.1.val.val i j + ((1/2) * knEntry v.2.1.val i j + v.2.2 / 24 * knEntry eta i j))
      simp only [knEntry, Matrix.smul_apply, smul_eq_mul]
      ring }).symm
private noncomputable def tracelessRicciCoords : TracelessRicci4 ≃ₗ[ℝ] (Fin 9 → ℝ) where
  toFun h := ![h.val 0 0, h.val 0 1, h.val 0 2, h.val 0 3, h.val 1 1,
    h.val 1 2, h.val 1 3, h.val 2 2, h.val 2 3]
  invFun v := ⟨!![v 0, v 1, v 2, v 3; v 1, v 4, v 5, v 6;
    v 2, v 5, v 7, v 8; v 3, v 6, v 8, v 0 - v 4 - v 7],
    fun i j => by fin_cases i <;> fin_cases j <;> rfl,
    by simp [lorentzTrace, diagSum, Fin.sum_univ_four]⟩
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl
  left_inv h := by
    have ht : -h.val 0 0 + h.val 1 1 + h.val 2 2 + h.val 3 3 = 0 := by
      simpa [lorentzTrace, diagSum, Fin.sum_univ_four] using h.property.2
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact h.property.1 _ _ | simp; linarith
  right_inv _ := by funext i; fin_cases i <;> rfl

/-- A symmetric Lorentzian trace-free Ricci form has nine free coordinates. -/
theorem finrank_tracelessRicci4 : finrank ℝ TracelessRicci4 = 9 := by
  simpa using tracelessRicciCoords.finrank_eq

def minkowski {K : Type*} [Ring K] (u v : Fin 4 → K) : K :=
  -(u 0 * v 0) + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

/-! ## Stereographic null directions and screens -/

/-- Finite stereographic coordinates and the south-pole ray. -/
abbrev FutureNullRay := Option ℂ

/-- The unnormalized future-directed null generator with Minkowski signature `(-+++)`. -/
def nullGenerator : FutureNullRay → Fin 4 → ℝ
  | none => ![1, 0, 0, -1]
  | some z => ![1 + z.normSq, 2 * z.re, 2 * z.im, 1 - z.normSq]

/-- The complex screen vector whose real and imaginary parts form the chosen frame. -/
def screenVector : FutureNullRay → Fin 4 → ℂ
  | none => ![0, 1, -Complex.I, 0]
  | some z => ![z, 1, Complex.I, -z]

/-- Orthonormal real screen frame specified by the complex chart vector. -/
def screenFrame (r : FutureNullRay) (a : Fin 2) : Fin 4 → ℝ :=
  ![fun i => (screenVector r i).re, fun i => (screenVector r i).im] a

theorem nullGenerator_future (r : FutureNullRay) :
    0 < nullGenerator r 0 ∧ minkowski (nullGenerator r) (nullGenerator r) = 0 := by
  cases r with
  | none => norm_num [nullGenerator, minkowski]
  | some z =>
    refine ⟨add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg z), ?_⟩
    simp [nullGenerator, minkowski, Complex.normSq_apply]; ring

theorem screenFrame_spec (r : FutureNullRay) :
    (∀ a, minkowski (screenFrame r a) (nullGenerator r) = 0) ∧
    (∀ a b, minkowski (screenFrame r a) (screenFrame r b) = if a = b then 1 else 0) := by
  refine ⟨?_, ?_⟩
  · intro a
    cases r <;> fin_cases a <;>
      simp [screenFrame, screenVector, nullGenerator, minkowski, Complex.normSq_apply] <;> ring
  · intro a b
    cases r <;> fin_cases a <;> fin_cases b <;>
      norm_num [screenFrame, screenVector, minkowski]
private def rayCoordinates (v : Fin 4 → ℝ) : ℝ × FutureNullRay :=
  if v 0 + v 3 = 0 then (v 0, none)
  else ((v 0 + v 3) / 2, some ⟨v 1 / (v 0 + v 3), v 2 / (v 0 + v 3)⟩)
private theorem rayCoordinates_scale (p : ℝ × FutureNullRay) (hp : 0 < p.1) :
    rayCoordinates (fun i => p.1 * nullGenerator p.2 i) = p := by
  rcases p with ⟨s, _ | z⟩
  · simp [rayCoordinates, nullGenerator]
  · change 0 < s at hp
    have h : s * (1 + z.normSq) + s * (1 - z.normSq) = 2 * s := by ring
    simp [rayCoordinates, nullGenerator, h, mul_ne_zero two_ne_zero hp.ne']
    congr 1 <;> field_simp

/-- Every future nonzero null vector has a unique positive scale and stereographic ray. -/
theorem future_null_ray (v : Fin 4 → ℝ) (ht : 0 < v 0) (hn : minkowski v v = 0) :
    ∃! p : ℝ × FutureNullRay, 0 < p.1 ∧ v = fun i => p.1 * nullGenerator p.2 i := by
  simp only [minkowski] at hn
  have hs : (v 0 + v 3) * (v 0 - v 3) = v 1 * v 1 + v 2 * v 2 := by linarith
  have hd : 0 ≤ v 0 + v 3 := by
    by_contra! h
    nlinarith [mul_neg_of_neg_of_pos h (show 0 < v 0 - v 3 by linarith),
      mul_self_nonneg (v 1), mul_self_nonneg (v 2)]
  refine ⟨rayCoordinates v, ?_, ?_⟩
  · by_cases h : v 0 + v 3 = 0
    · have h1 : v 1 = 0 := by nlinarith [mul_self_nonneg (v 2)]
      have h2 : v 2 = 0 := by nlinarith [mul_self_nonneg (v 1)]
      refine ⟨by simpa [rayCoordinates, h] using ht, ?_⟩
      funext i
      fin_cases i <;> simp [rayCoordinates, h, nullGenerator, h1, h2]
      linarith
    · let z : ℂ := ⟨v 1 / (v 0 + v 3), v 2 / (v 0 + v 3)⟩
      have hz : (v 0 + v 3) * z.normSq = v 0 - v 3 := by
        simp only [Complex.normSq_apply, z]
        field_simp
        nlinarith
      refine ⟨by simpa [rayCoordinates, h] using half_pos (lt_of_le_of_ne hd (Ne.symm h)), ?_⟩
      simp only [rayCoordinates, ite_eq_right h]
      change v = fun i => ((v 0 + v 3) / 2) * nullGenerator (some z) i
      funext i
      fin_cases i <;> simp [nullGenerator]
      all_goals first | nlinarith | dsimp [z]; field_simp
  · intro p hp
    rw [hp.2, rayCoordinates_scale p hp.1]

/-- Degree at most four, with infinity evaluated in the degree-four trivialization. -/
abbrev WeylQuartic := Polynomial.degreeLT ℂ 5

/-- A projective quartic has value `p(z)` in the finite chart and coefficient `p₄` at infinity. -/
def quarticEval (ray : FutureNullRay) : WeylQuartic →ₗ[ℂ] ℂ :=
  (ray.elim (lcoeff ℂ 4) leval).comp (Polynomial.degreeLT ℂ 5).subtype

/-- Simultaneous quartic evaluation with the chosen generator of each projective point. -/
def projectiveEval {N : ℕ} (ray : Fin N → FutureNullRay) : WeylQuartic →ₗ[ℂ] (Fin N → ℂ) :=
  LinearMap.pi fun j => quarticEval (ray j)
private def finiteNodes {N : ℕ} (ray : Fin N → FutureNullRay) : Finset (Fin N) :=
  Finset.univ.filter fun j => (ray j).isSome
private theorem finiteNodes_card_lt {N : ℕ} {ray : Fin N → FutureNullRay}
    {i : Fin N} (hi : ray i = none) : (finiteNodes ray).card < N := by
  simpa using Finset.card_lt_univ_of_notMem (show i ∉ finiteNodes ray by simp [finiteNodes, hi])
private def projectiveInterpolate {N : ℕ} {ray : Fin N → FutureNullRay}
    (hr : Function.Injective ray) (hN : N ≤ 5) (f : Fin N → ℂ) :
    {p : WeylQuartic // projectiveEval ray p = f} := by
  classical
  let s := finiteNodes ray
  let z := fun j => (ray j).getD 0
  let t := if h : ∃ j, ray j = none then f h.choose else 0
  have hsome (i : Fin N) (hi : i ∈ s) : ray i = some (z i) := by
    have hs : (ray i).isSome := (Finset.mem_filter.mp hi).2
    rw [show z i = (ray i).get hs from (Option.get_eq_getD (ray i)).symm]
    exact Option.eq_some_of_isSome hs
  have hz : Set.InjOn z s := fun i hi j hj hij => hr ((hsome i hi).trans (hij ▸ (hsome j hj).symm))
  let p := Lagrange.interpolate s z fun j => f j - t * z j ^ 4
  have hp : p.degree < (s.card : WithBot ℕ) := Lagrange.degree_interpolate_lt _ hz
  have hp₅ : p ∈ WeylQuartic := mem_degreeLT.mpr <| hp.trans_le
    (by exact_mod_cast (card_finset_fin_le s).trans hN)
  refine ⟨⟨p, hp₅⟩ + ⟨monomial 4 t, monomial_coe_mem_degreeLT (4 : Fin 5) t⟩, ?_⟩
  funext i
  cases hi : ray i with
  | some a =>
    have hv := Lagrange.eval_interpolate_at_node (r := fun j => f j - t * z j ^ 4) hz
      (show i ∈ s by simp [s, finiteNodes, hi])
    simpa [projectiveEval, quarticEval, hi, p, z, eval_monomial] using eq_sub_iff_add_eq.mp hv
  | none =>
    have h' : ∃ j, ray j = none := ⟨i, hi⟩
    have hc : s.card ≤ 4 := Nat.lt_succ_iff.mp ((finiteNodes_card_lt hi).trans_le hN)
    have hcoef : p.coeff 4 = 0 := coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hc))
    simp [projectiveEval, quarticEval, hi, hcoef, t, h', hr (h'.choose_spec.trans hi.symm)]
private theorem projectiveEval_surjective {N : ℕ} {ray : Fin N → FutureNullRay}
    (hr : Function.Injective ray) (hN : N ≤ 5) :
    Function.Surjective (projectiveEval ray) :=
  fun f => ⟨(projectiveInterpolate hr hN f).val, (projectiveInterpolate hr hN f).property⟩
private theorem finrank_weylQuartic_complex : finrank ℂ WeylQuartic = 5 := by
  simpa using (Polynomial.degreeLTEquiv ℂ 5).finrank_eq
private theorem projectiveEval_injective {N : ℕ} {ray : Fin N → FutureNullRay}
    (hr : Function.Injective ray) (hN : 5 ≤ N) :
    Function.Injective (projectiveEval ray) := by
  let e := Fin.castLEEmb hN
  have hinj : Function.Injective (projectiveEval (ray ∘ e)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_weylQuartic_complex]; simp)).mpr
      (projectiveEval_surjective (hr.comp e.injective) le_rfl)
  intro p q hpq
  apply hinj
  exact funext fun i => congrFun hpq (e i)
private def projectiveVanishing {N : ℕ} (ray : Fin N → FutureNullRay) (hN : N ≤ 4) :
    {p : WeylQuartic // projectiveEval ray p = 0 ∧ p ≠ 0} := by
  let s := finiteNodes ray
  let z := fun i => (ray i).getD (0 : ℂ)
  let p := Lagrange.nodal s z
  have hp : p.degree = (s.card : WithBot ℕ) := Lagrange.degree_nodal
  have hp₅ : p ∈ WeylQuartic := mem_degreeLT.mpr (hp ▸
    (by exact_mod_cast (card_finset_fin_le s).trans_lt (by omega : N < 5)))
  refine ⟨⟨p, hp₅⟩, funext fun i => ?_, fun h => Lagrange.nodal_ne_zero
    (s := s) (v := z) (congrArg (fun q : WeylQuartic => (q : ℂ[X])) h)⟩
  cases hi : ray i with
  | none =>
    have hcoef : p.coeff 4 = 0 := coeff_eq_zero_of_degree_lt (hp ▸
      (by exact_mod_cast (finiteNodes_card_lt hi).trans_le hN))
    simpa [projectiveEval, quarticEval, hi] using hcoef
  | some a =>
    have h := Lagrange.eval_nodal_at_node (v := z) (show i ∈ s by simp [s, finiteNodes, hi])
    simpa [projectiveEval, quarticEval, hi, z, p] using h
private noncomputable def quarticForward (u : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![2 * (u 0 - u 1) + 4 * Complex.I * u 2,
    -8 * u 3 - 8 * Complex.I * u 4,
    -12 * (u 0 + u 1),
    8 * u 3 - 8 * Complex.I * u 4,
    2 * (u 0 - u 1) - 4 * Complex.I * u 2]
/-- The quartic coefficients in ascending degree from the entries a, b, c, d, e of
the complex symmetric trace-free matrix E − iM. -/
private noncomputable def quarticCoeffs : (Fin 5 → ℂ) ≃ₗ[ℂ] (Fin 5 → ℂ) where
  toFun := quarticForward
  invFun p := ![(p 0 + p 4) / 8 - p 2 / 24, -(p 0 + p 4) / 8 - p 2 / 24,
    -(p 0 - p 4) * Complex.I / 8, (p 3 - p 1) / 16, (p 1 + p 3) * Complex.I / 16]
  left_inv u := by
    funext i
    fin_cases i <;> simp [quarticForward] <;> ring_nf <;>
      simp [Complex.I_sq]
  right_inv p := by
    funext i
    fin_cases i <;> simp [quarticForward] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring
  map_add' u v := by
    funext i
    fin_cases i <;> simp [quarticForward] <;> ring
  map_smul' a u := by
    funext i
    fin_cases i <;> simp [quarticForward, Pi.smul_apply, smul_eq_mul] <;> ring
private noncomputable def stfCoords : STF3 ℝ ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun A := ![A.val 0 0, A.val 1 1, A.val 0 1, A.val 0 2, A.val 1 2]
  invFun a := ⟨!![a 0, a 2, a 3; a 2, a 1, a 4; a 3, a 4, -a 0 - a 1],
    fun i j => by fin_cases i <;> fin_cases j <;> rfl,
    by simp [diagSum, Fin.sum_univ_three]⟩
  left_inv A := by
    apply Subtype.ext
    have h := A.property.2
    simp [diagSum, Fin.sum_univ_three] at h
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact (A.property.1 _ _) | linarith!
  right_inv a := by funext i; fin_cases i <;> rfl
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl
private noncomputable def chiralCoords : Weyl4 ≃ₗ[ℝ] (Fin 5 → ℂ) :=
  let zip : ((Fin 5 → ℝ) × (Fin 5 → ℝ)) ≃ₗ[ℝ] (Fin 5 → ℝ × ℝ) :=
    { (Equiv.arrowProdEquivProdArrow (Fin 5) (fun _ => ℝ) (fun _ => ℝ)).symm with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  weyl_electric_magnetic_equiv.trans <|
    (stfCoords.prodCongr (stfCoords.trans (LinearEquiv.neg ℝ))).trans <|
      zip.trans (LinearEquiv.piCongrRight fun _ => Complex.equivRealProdLm.symm)
instance : SMul ℂ Weyl4 := ⟨fun a C => chiralCoords.symm (a • chiralCoords C)⟩
instance : Module ℂ Weyl4 :=
  Function.Injective.module ℂ chiralCoords.toAddEquiv.toAddMonoidHom chiralCoords.injective
    fun _ _ => chiralCoords.apply_symm_apply _
instance : IsScalarTower ℝ ℂ Weyl4 where
  smul_assoc a b C := chiralCoords.injective (by
    change chiralCoords (chiralCoords.symm ((a • b) • chiralCoords C)) =
      chiralCoords (a • chiralCoords.symm (b • chiralCoords C))
    rw [LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply, smul_assoc])

/-- The complex structure is induced by the chiral coordinates E − iM. -/
noncomputable def weylQuarticEquiv : Weyl4 ≃ₗ[ℂ] WeylQuartic :=
  let e : Weyl4 ≃ₗ[ℂ] (Fin 5 → ℂ) :=
    { chiralCoords.toAddEquiv with
      map_smul' := fun a C => chiralCoords.apply_symm_apply (a • chiralCoords C) }
  e.trans (quarticCoeffs.trans (Polynomial.degreeLTEquiv ℂ 5).symm)

theorem finrank_weyl4 : Module.finrank ℝ Weyl4 = 10 := by
  rw [chiralCoords.finrank_eq, finrank_real_of_complex, Module.finrank_fin_fun]

theorem finrank_algebraicCurvature4 : Module.finrank ℝ AlgebraicCurvature4 = 20 := by
  let : Module.Free ℝ Weyl4 := Module.Free.of_equiv chiralCoords.symm
  let : Module.Free ℝ TracelessRicci4 := Module.Free.of_equiv tracelessRicciCoords.symm
  rw [curvature_ricci_split.finrank_eq, Module.finrank_prod, Module.finrank_prod,
    finrank_weyl4, finrank_tracelessRicci4, Module.finrank_self]
private def wedge {K : Type*} [Ring K] (u v : Fin 4 → K) (i : PairIndex) : K :=
  u (pairLeft i) * v (pairRight i) - u (pairRight i) * v (pairLeft i)
private def pairBilinear {K ι : Type*} [CommRing K] [Fintype ι]
    (C : Matrix ι ι K) (u v : ι → K) : K :=
  ∑ i, ∑ j, C i j * u i * v j

/-- The real null tidal form evaluated on two screen vectors. -/
def tidal (R : AlgebraicCurvature4) (k a b : Fin 4 → ℝ) : ℝ :=
  pairBilinear R.val (wedge a k) (wedge b k)

/-- The complex contraction on the chosen null generator and screen vector. -/
def complexTide (R : AlgebraicCurvature4) (r : FutureNullRay) : ℂ :=
  let u := wedge (screenVector r) (fun i => (nullGenerator r i : ℂ))
  pairBilinear (fun i j => (R.val i j : ℂ)) u u
private theorem tidal_symm (R : AlgebraicCurvature4) (k a b : Fin 4 → ℝ) :
    tidal R k a b = tidal R k b a := by
  unfold tidal pairBilinear
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [R.property.1 j i, mul_right_comm]
/-- Contracting a Kulkarni–Nomizu lift against a null screen leaves its metric term. -/
private theorem tidal_kn (h : Matrix (Fin 4) (Fin 4) ℝ) (hs : ∀ i j, h i j = h j i)
    (k a b : Fin 4 → ℝ) :
    tidal (kn h hs) k a b = minkowski a b * pairBilinear h k k +
      minkowski k k * pairBilinear h a b - minkowski a k * pairBilinear h k b -
      minkowski k b * pairBilinear h a k := by
  simp [tidal, pairBilinear, kn, knEntry, wedge, pairLeft, pairRight, eta, diagonal_apply,
    minkowski, Fintype.sum_sum_type, Fin.sum_univ_succ, hs 1 0, hs 2 0, hs 3 0, hs 2 1,
    hs 3 1, hs 3 2]
  ring
private theorem tidal_trace (R : AlgebraicCurvature4) (r : FutureNullRay) :
    tidal R (nullGenerator r) (screenFrame r 0) (screenFrame r 0) +
      tidal R (nullGenerator r) (screenFrame r 1) (screenFrame r 1) =
      pairBilinear (ricci R) (nullGenerator r) (nullGenerator r) := by
  have hs (i j : PairIndex) : R.val i j = R.val j i := R.property.1 i j
  cases r <;> simp [tidal, pairBilinear, wedge, pairLeft, pairRight, nullGenerator,
    screenFrame, screenVector, Fintype.sum_sum_type, Fin.sum_univ_succ, ricci, contractions,
    electric, magnetic, spatial, Complex.normSq_apply, hs (.inl 1) (.inl 0),
    hs (.inl 2) (.inl 0), hs (.inl 2) (.inl 1), hs (.inr 1) (.inr 0),
    hs (.inr 2) (.inr 0), hs (.inr 2) (.inr 1), fun i j => hs (.inr i) (.inl j)] <;> ring

/-- The complex tide combines the two independent trace-free real tidal entries. -/
theorem complexTide_weyl (C : Weyl4) (r : FutureNullRay) :
    let T := fun a b => tidal C.val (nullGenerator r) (screenFrame r a) (screenFrame r b)
    complexTide C.val r = 2 * ((T 0 0 : ℂ) + Complex.I * (T 0 1 : ℂ)) := by
  have ht := tidal_trace C.val r
  simp [LinearMap.mem_ker.mp C.property, pairBilinear] at ht
  have hs := tidal_symm C.val (nullGenerator r) (screenFrame r 1) (screenFrame r 0)
  simp only [tidal, pairBilinear, wedge, screenFrame, Matrix.cons_val_zero, Matrix.cons_val_one] at ht hs
  apply Complex.ext <;>
    simp only [tidal, complexTide, pairBilinear, wedge, screenFrame, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.re_sum, Complex.im_sum, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, add_zero, zero_add,
      Finset.sum_sub_distrib, Finset.sum_add_distrib] <;> linarith

/-- Each real screen entry has the same Ricci trace shift, with zero off-diagonal shift.
The trace-free part is the Weyl tide. -/
theorem null_tidal_ricci_invariance (R : AlgebraicCurvature4) (r : FutureNullRay) :
    let k := nullGenerator r
    let e := screenFrame r
    let T := fun Q a b => tidal Q k (e a) (e b)
    let W := (curvature_ricci_split R).1.val
    ∀ a b, T R a b = T W a b + (if a = b then 1 else 0) * pairBilinear (ricci R) k k / 2 ∧
      T R a b - (if a = b then 1 else 0) * (T R 0 0 + T R 1 1) / 2 = T W a b := by
  dsimp only
  intro a b
  let k := nullGenerator r
  let e := screenFrame r
  have hk : minkowski k k = 0 := (nullGenerator_future r).2
  have ha : minkowski (e a) k = 0 := (screenFrame_spec r).1 a
  have he : minkowski (e a) (e b) = (if a = b then 1 else 0) := (screenFrame_spec r).2 a b
  have hb : minkowski k (e b) = 0 := by
    simpa [k, e, minkowski, mul_comm] using (screenFrame_spec r).1 b
  have hη : pairBilinear eta k k = 0 := by
    simpa [pairBilinear, eta, diagonal_apply, Fin.sum_univ_succ, minkowski, add_assoc] using hk
  have hS : pairBilinear (ricciTF R).val k k = pairBilinear (ricci R) k k := by
    simp only [ricciTF, pairBilinear, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    simp only [← mul_assoc]
    change _ - _ * pairBilinear eta k k = _
    rw [hη, mul_zero, sub_zero]
  let L := kn (ricciTF R).val (ricciTF R).property.1
  let W := (curvature_ricci_split R).1.val
  let s := lorentzTrace (ricci R)
  have h := congrArg (fun Q => tidal Q k (e a) (e b)) (curvature_ricci_split.symm_apply_apply R)
  change tidal (W + ((1 / 2 : ℝ) • L + (s / 24) • kn eta eta_symm)) k (e a) (e b) = _ at h
  simp only [tidal, pairBilinear, AddMemClass.coe_add, SetLike.val_smul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at h
  simp only [← mul_assoc] at h
  change tidal W k (e a) (e b) + ((1 / 2) * tidal L k (e a) (e b) +
    (s / 24) * tidal (kn eta eta_symm) k (e a) (e b)) = tidal R k (e a) (e b) at h
  simp only [L, tidal_kn, hk, ha, hb, he, hS, hη, mul_zero, zero_mul, sub_zero, add_zero] at h
  dsimp only [k, e, W] at h
  exact ⟨by linarith, by rw [tidal_trace]; linarith⟩
private noncomputable def bivectorX : FutureNullRay → Fin 3 → ℂ
  | none => ![-1, Complex.I, 0]
  | some z => ![z ^ 2 - 1, -Complex.I * (z ^ 2 + 1), 2 * z]
private theorem screen_wedge (r : FutureNullRay) (i : PairIndex) :
    wedge (screenVector r) (fun a => (nullGenerator r a : ℂ)) i =
      i.elim (bivectorX r) (fun j => -Complex.I * bivectorX r j) := by
  rcases r with _ | z <;> rcases i with i | i <;> fin_cases i <;>
    apply Complex.ext <;>
    norm_num [wedge, pairLeft, pairRight, screenVector, nullGenerator, bivectorX,
      Complex.normSq_apply, pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.add_im, Complex.sub_im, Complex.mul_im] <;> (try ring)

/-- The geometric contractions agree with the projective quartic on both charts. -/
theorem weylQuarticEquiv_eval (C : Weyl4) (r : FutureNullRay) :
    quarticEval r (weylQuarticEquiv C) = complexTide C.val r := by
  let E := electricPart C
  let M := magneticPart C
  have hC : C.val.val = emBlock E.val M.val :=
    congrArg (fun D : Weyl4 => D.val.val) (weyl_electric_magnetic_equiv.left_inv C).symm
  have tr (A : STF3 ℝ) : A.val 2 2 = -A.val 0 0 - A.val 1 1 := by
    have h := A.property.2
    simp [diagSum, Fin.sum_univ_three] at h
    linarith
  have hc (i : Fin 5) : chiralCoords C i = (stfCoords E i : ℂ) - Complex.I * (stfCoords M i : ℂ) := by
    change Complex.equivRealProdLm.symm (stfCoords E i, -stfCoords M i) = _
    rw [Complex.equivRealProdLm_symm_apply, Complex.ofReal_neg]
    ring
  let p := weylQuarticEquiv C
  have hp : Polynomial.degreeLTEquiv ℂ 5 p = quarticForward (chiralCoords C) :=
    (Polynomial.degreeLTEquiv ℂ 5).apply_symm_apply _
  have h (r : FutureNullRay) : quarticEval r p =
      r.elim (quarticForward (chiralCoords C) 4)
        (fun z => ∑ i : Fin 5, quarticForward (chiralCoords C) i * z ^ (i : ℕ)) := by
    cases r with
    | none => exact congrFun hp 4
    | some z => rw [← hp]; exact Polynomial.eval_eq_sum_degreeLTEquiv p.property z
  change quarticEval r p = _
  rw [h r]
  simp only [complexTide, screen_wedge, pairBilinear, hC, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, emBlock, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.neg_apply, Complex.ofReal_neg]
  cases r <;> simp [Fin.sum_univ_succ, quarticForward, hc, stfCoords, bivectorX, tr E, tr M,
    E.property.1 1 0, E.property.1 2 0, E.property.1 2 1, M.property.1 1 0, M.property.1 2 0,
    M.property.1 2 1] <;> ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring

/-- Complex amplitudes of the null screen tides at the chosen rays. -/
def nullTidalSample {N : ℕ} (ray : Fin N → FutureNullRay) : Weyl4 →ₗ[ℝ] (Fin N → ℂ) :=
  ((projectiveEval ray).restrictScalars ℝ).comp
    (weylQuarticEquiv.restrictScalars ℝ).toLinearMap

/-- Distinct null rays give independent real tide constraints up to the ten Weyl coordinates. -/
theorem weyl_null_screen_sampling {N : ℕ} (ray : Fin N → FutureNullRay)
    (hr : Function.Injective ray) :
    finrank ℝ (LinearMap.range (nullTidalSample ray)) = min 10 (2 * N) ∧
    finrank ℝ (LinearMap.ker (nullTidalSample ray)) = max 0 (10 - 2 * N) := by
  have hRank : finrank ℝ (LinearMap.range (nullTidalSample ray)) = min 10 (2 * N) := by
    by_cases hN : N ≤ 5
    · have hs : Function.Surjective (nullTidalSample ray) :=
        (projectiveEval_surjective hr hN).comp weylQuarticEquiv.surjective
      rw [LinearMap.range_eq_top.mpr hs, finrank_top, finrank_real_of_complex, Module.finrank_fin_fun]
      omega
    · have hi : Function.Injective (nullTidalSample ray) :=
        (projectiveEval_injective hr (by omega)).comp weylQuarticEquiv.injective
      rw [LinearMap.finrank_range_of_inj hi, finrank_weyl4]
      omega
  have h := LinearMap.finrank_range_add_finrank_ker (K := ℝ) (V := Weyl4) (V₂ := Fin N → ℂ) (nullTidalSample ray)
  rw [hRank, finrank_weyl4] at h
  exact ⟨hRank, by omega⟩

/-- The tidal samples on any five distinct future null rays reconstruct the Weyl tensor. -/
def weyl_null_screen_five (ray : Fin 5 → FutureNullRay) (hr : Function.Injective ray) :
    Weyl4 ≃ₗ[ℝ] (Fin 5 → ℂ) where
  toFun := nullTidalSample ray
  invFun f := weylQuarticEquiv.symm (projectiveInterpolate hr le_rfl f).val
  left_inv C := by
    apply weylQuarticEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact projectiveEval_injective hr le_rfl
      (projectiveInterpolate hr le_rfl (nullTidalSample ray C)).property
  right_inv f := by
    change projectiveEval ray (weylQuarticEquiv (weylQuarticEquiv.symm _)) = f
    simpa only [LinearEquiv.apply_symm_apply] using (projectiveInterpolate hr le_rfl f).property
  map_add' := (nullTidalSample ray).map_add
  map_smul' := (nullTidalSample ray).map_smul

/-- Vanishing on five distinct null screens forces the Weyl tensor to be zero. -/
theorem weyl_null_screen_zero (ray : Fin 5 → FutureNullRay) (hr : Function.Injective ray)
    (C : Weyl4) : nullTidalSample ray C = 0 ↔ C = 0 := by
  change weyl_null_screen_five ray hr C = 0 ↔ C = 0
  rw [← map_zero (weyl_null_screen_five ray hr), (weyl_null_screen_five ray hr).injective.eq_iff]
/-- The inverse quartic image of the product of the finite nodal factors. -/
def vanishingWeyl {N : ℕ} (ray : Fin N → FutureNullRay) (hN : N ≤ 4) : Weyl4 :=
  weylQuarticEquiv.symm (projectiveVanishing ray hN).val

/-- Every configuration of at most four rays has a nonzero Weyl tensor invisible to the samples. -/
theorem weyl_null_screen_vanishing {N : ℕ} (ray : Fin N → FutureNullRay) (hN : N ≤ 4) :
    nullTidalSample ray (vanishingWeyl ray hN) = 0 ∧ vanishingWeyl ray hN ≠ 0 := by
  have h := (projectiveVanishing ray hN).property
  refine ⟨?_, ?_⟩
  · change projectiveEval ray (weylQuarticEquiv (weylQuarticEquiv.symm _)) = 0
    simpa only [LinearEquiv.apply_symm_apply] using h.1
  · intro he
    exact h.2 (by simpa [vanishingWeyl] using congrArg weylQuarticEquiv he)

end D5.S3.Geometry.Lorentz.WeylNullScreen
