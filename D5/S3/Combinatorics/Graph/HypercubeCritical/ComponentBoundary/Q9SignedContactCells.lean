/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Signed two-direction contacts cancel on each parity and two-bit cell. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas

/-! Signed contact obstructions for the separated cubic branch of Hong, Wu and
Xia's Problem 2, arXiv:2610.09483. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells

noncomputable section

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip flip_adj gamma gamma_apply
  IsSwitching switchingVector switching_sq ambient_eigenvector anticommutator)
open BalancedCubeGirth (gamma_anticommute)
open TwentyPointEightWord (gamma_square)
open Q9BoundaryGram (Interior Exterior)
open Q9IsotropicHuang (parity weightedLinear)
open private huangMatrix huangMatrix_symmetric cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private regular_parity_card cube_opposite_card interior_card degree_of_no_exterior_neighbors
  from D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram
open private paritySide from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private weightedLinear_square weightedLinear_apply flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private adjacent_exists_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

private abbrev Vec := Q 9 → ℝ
open Classical in
private abbrev Cubic (S : Finset (Q 9)) :=
  ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3
private abbrev Connected (S : Finset (Q 9)) :=
  ((hypercube 9).induce (S : Set (Q 9))).Connected
private abbrev Separated (C D : Finset (Q 9)) :=
  ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y
private abbrev Supported (S : Finset (Q 9)) (f : Vec) := ∀ x ∉ S, f x = 0
private abbrev OnParity (b : Bool) (f : Vec) := ∀ x, parity x ≠ b → f x = 0

/-- Retain the specified parity of a switching vector or cube function. -/
def parityPart (b : Bool) : Vec →ₗ[ℝ] Vec :=
  LinearMap.pi fun x => if parity x = b then LinearMap.proj x else 0

private theorem parityPart_apply (b : Bool) (f : Vec) (x : Q 9) :
    parityPart b f x = if parity x = b then f x else 0 := by
  by_cases hx : parity x = b <;> simp [parityPart, hx]

private def supportPart (S : Finset (Q 9)) : Vec →ₗ[ℝ] Vec :=
  LinearMap.pi fun x => if x ∈ S then LinearMap.proj x else 0

private theorem supportPart_apply (S : Finset (Q 9)) (f : Vec) (x : Q 9) :
    supportPart S f x = if x ∈ S then f x else 0 := by
  by_cases hx : x ∈ S <;> simp [supportPart, hx]

private theorem opposite_eq {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

private abbrev H : Vec →ₗ[ℝ] Vec := Matrix.toLin' (huangMatrix 9)

private theorem weighted_sum (w : Fin 9 → ℝ) (f : Vec) :
    weightedLinear w f = ∑ k, w k • gamma k f := by
  ext x
  simp [weightedLinear_apply, Q9IsotropicHuang.weightedAction, gamma_apply, flipSign_cast,
    mul_assoc]

private theorem unit_weight (f : Vec) : weightedLinear (fun _ => (1 : ℝ)) f = H f := by
  classical
  ext x
  simp only [weighted_sum, one_smul, Finset.sum_apply, gamma_apply]
  change _ = ∑ y, huangMatrix 9 x y * f y
  let e : Fin 9 ↪ Q 9 := ⟨flip x, flip_injective x⟩
  calc
    _ = ∑ y ∈ Finset.univ.map e, huangMatrix 9 x y * f y :=
      (Finset.sum_map Finset.univ e (fun y => huangMatrix 9 x y * f y)).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      have hn : ¬ (hypercube 9).Adj x y := by
        intro ha
        obtain ⟨k, hk⟩ := adjacent_exists_flip ha
        exact hy (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, hk.symm⟩)
      rw [SupportedEigenSaturation.matrix_eq_zero_of_not_adj hn, zero_mul]

private theorem gamma_selfAdjoint (k : Fin 9) (f g : Vec) :
    gamma k f ⬝ᵥ g = f ⬝ᵥ gamma k g := by
  let e : Q 9 ≃ Q 9 := (show Function.Involutive (fun x : Q 9 => flip x k) from
    fun x => BalancedCriticalSpectrum.flip_flip x k).toPerm _
  unfold dotProduct
  refine Fintype.sum_equiv e _ _ fun x => ?_
  change gamma k f x * g x = f (flip x k) * gamma k g (flip x k)
  rw [gamma_apply, gamma_apply, BalancedCriticalSpectrum.flip_flip,
    huangMatrix_symmetric (flip x k) x]
  ring

private theorem weighted_selfAdjoint (w : Fin 9 → ℝ) (f g : Vec) :
    weightedLinear w f ⬝ᵥ g = f ⬝ᵥ weightedLinear w g := by
  simp only [weighted_sum, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, gamma_selfAdjoint]

private theorem weighted_cross (w : Fin 9 → ℝ) {b : Bool} {f : Vec}
    (hf : OnParity b f) : OnParity (!b) (weightedLinear w f) := by
  intro x hx
  have hb : parity x = b := by
    have h := opposite_eq hx
    simpa using h
  simp only [weighted_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gamma_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [hf _ (fun h => cubeParity_ne_of_adj (flip_adj x k) (hb.trans h.symm)), mul_zero, mul_zero]

private theorem weighted_separated {C D : Finset (Q 9)} (hsep : Separated C D)
    (w : Fin 9 → ℝ) {f : Vec} (hf : Supported D f) : ∀ x ∈ C, weightedLinear w f x = 0 := by
  intro x hx
  simp only [weighted_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gamma_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [hf _ (fun hy => hsep x hx _ hy (flip_adj x k)), mul_zero, mul_zero]

private theorem dot_disjoint {C D : Finset (Q 9)} (hdisj : Disjoint C D)
    {f g : Vec} (hf : Supported C f) (hg : Supported D g) : f ⬝ᵥ g = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ C
  · rw [hg _ (fun hy => Finset.disjoint_left.mp hdisj hx hy), mul_zero]
  · rw [hf _ hx, zero_mul]

private theorem gamma_separated {C D : Finset (Q 9)} (hsep : Separated C D) (k : Fin 9)
    {f g : Vec} (hf : Supported C f) (hg : Supported D g) : f ⬝ᵥ gamma k g = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ C
  · rw [gamma_apply, hg _ (fun hy => hsep x hx _ hy (flip_adj x k)), mul_zero, mul_zero]
  · rw [hf _ hx, zero_mul]

private theorem parity_eigen (C : Finset (Q 9)) (s : Vec) (hr : Cubic C)
    (hs : IsSwitching C s) (b : Bool) :
    H (parityPart b (switchingVector C s)) = (3 : ℝ) • parityPart (!b) (switchingVector C s) := by
  have he := ambient_eigenvector (d := 3) C s hr hs
  ext x
  by_cases hx : parity x = !b
  · change (∑ y, huangMatrix 9 x y * parityPart b (switchingVector C s) y) = _
    simp only [Pi.smul_apply, smul_eq_mul, parityPart_apply, ite_eq_left hx]
    rw [← show H (switchingVector C s) x = 3 * switchingVector C s x from congrFun he x]
    change _ = ∑ y, huangMatrix 9 x y * switchingVector C s y
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : parity y = b
    · rw [ite_eq_left hy]
    · rw [ite_eq_right hy, SupportedEigenSaturation.matrix_eq_zero_of_not_adj
        (fun ha => cubeParity_ne_of_adj ha (hx.trans (opposite_eq hy).symm)), zero_mul, zero_mul]
  · change H _ x = _
    rw [← unit_weight, weighted_cross _ (fun y hy => by simp [parityPart_apply, hy]) x hx]
    simp [parityPart_apply, hx]

private theorem weighted_square (w : Fin 9 → ℝ) (f : Vec) :
    weightedLinear w (weightedLinear w f) = (∑ k, w k ^ 2) • f := by
  simpa only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] using
    congrArg (fun A : Module.End ℝ Vec => A f) (weightedLinear_square w)

/-- A crossing-kernel vector on one connected component is a multiple of its
parity switch at the unit weights. -/
private theorem unit_line {S : Finset (Q 9)} (hr : Cubic S) (hc : Connected S)
    {s : Vec} (hs : IsSwitching S s) {b : Bool} {f : Vec}
    (hf : Supported S f) (hfb : OnParity b f) (hHf : Supported S (H f))
    (root : Q 9) (hroot : root ∈ S) (hpar : parity root = b) :
    f = (f root * s root) • parityPart b (switchingVector S s) := by
  let z := f + (1 / 3 : ℝ) • H f
  have hz : Supported S z := by
    intro x hx
    change f x + (1 / 3 : ℝ) * H f x = 0
    rw [hf x hx, hHf x hx, mul_zero, add_zero]
  have hsq : H (H f) = (9 : ℝ) • f := by
    simpa [unit_weight] using weighted_square (fun _ => (1 : ℝ)) f
  have he : H z = (3 : ℝ) • z := by
    dsimp only [z]
    rw [map_add, map_smul, hsq, smul_add, smul_smul, smul_smul]
    norm_num [add_comm]
  have he' : (huangMatrix 9).mulVec z = ((3 : ℕ) : ℝ) • z := he
  have heq (x y : (S : Set (Q 9)))
      (ha : ((hypercube 9).induce (S : Set (Q 9))).Adj x y) :
      z x.1 * s x.1 = z y.1 * s y.1 := by
    have hstep := SupportedEigenSaturation.edge_identity S z
      (fun a => (hr a).le) hz he' x.property y.property ha
    rw [hs.2 x.1 x.property y.1 y.property ha] at hstep
    calc
      _ = s x.1 ^ 2 * (z y.1 * s y.1) := by rw [hstep]; ring
      _ = _ := by rw [switching_sq hs x.property, one_mul]
  have hrootz : z root = f root := by
    have h0 : H f root = 0 := by
      rw [← unit_weight]
      exact weighted_cross _ hfb root (by rw [hpar]; cases b <;> decide)
    change f root + (1 / 3 : ℝ) * H f root = f root
    rw [h0, mul_zero, add_zero]
  ext x
  by_cases hx : x ∈ S
  · by_cases hb : parity x = b
    · obtain ⟨walk⟩ := hc.preconnected (⟨x, hx⟩ : (S : Set (Q 9))) ⟨root, hroot⟩
      have hw {p q : (S : Set (Q 9))}
          (w : ((hypercube 9).induce (S : Set (Q 9))).Walk p q) :
          z p.1 * s p.1 = z q.1 * s q.1 := by
        induction w with
        | nil => rfl
        | cons ha _ ih => exact (heq _ _ ha).trans ih
      have hxz : z x = f x := by
        have h0 : H f x = 0 := by
          rw [← unit_weight]
          exact weighted_cross _ hfb x (by rw [hb]; cases b <;> decide)
        change f x + (1 / 3 : ℝ) * H f x = f x
        rw [h0, mul_zero, add_zero]
      have h := hw walk
      change z x * s x = z root * s root at h
      rw [hxz, hrootz] at h
      simp only [Pi.smul_apply, smul_eq_mul, parityPart_apply, ite_eq_left hb,
        switchingVector, ite_eq_left hx]
      calc
        f x = (f x * s x) * s x := by
          rw [mul_assoc, ← pow_two, switching_sq hs hx, mul_one]
        _ = _ := by rw [h]
    · simp [hfb x hb, parityPart_apply, hb]
  · simp [hf x hx, parityPart_apply, switchingVector, hx]

private theorem split_crossing {C D : Finset (Q 9)} (hdisj : Disjoint C D)
    (hsep : Separated C D) (w : Fin 9 → ℝ) {f g : Vec}
    (hf : Supported C f) (hg : Supported D g)
    (hout : Supported (C ∪ D) (weightedLinear w (f + g))) :
    Supported C (weightedLinear w f) ∧ Supported D (weightedLinear w g) := by
  let u := weightedLinear w f
  let v := weightedLinear w g
  have horth : u ⬝ᵥ v = 0 := by
    change weightedLinear w f ⬝ᵥ weightedLinear w g = _
    rw [weighted_selfAdjoint, weighted_square, dotProduct_smul, dot_disjoint hdisj hf hg, smul_zero]
  have hCD : ∀ x ∈ C, v x = 0 := weighted_separated hsep w hg
  have hDC : ∀ x ∈ D, u x = 0 :=
    weighted_separated (fun x hx y hy ha => hsep y hy x hx ha.symm) w hf
  have hneg (x : Q 9) (hx : x ∉ C ∪ D) : u x + v x = 0 := by
    simpa only [map_add, Pi.add_apply] using hout x hx
  have hsum : (∑ x, if x ∈ C ∪ D then 0 else (u x) ^ 2) = 0 := by
    calc
      _ = ∑ x, -(u x * v x) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ C ∪ D
        · rcases Finset.mem_union.mp hx with h | h
          · simp [hx, hCD x h]
          · simp [hx, hDC x h]
        · simp only [ite_eq_right hx]
          have hv : v x = -u x := by linarith [hneg x hx]
          rw [hv]
          ring
      _ = 0 := by rw [Finset.sum_neg_distrib]; exact neg_eq_zero.mpr horth
  have hz (x : Q 9) (hx : x ∉ C ∪ D) : u x = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x (_ : x ∈ (Finset.univ : Finset (Q 9))) => by split_ifs <;> positivity)).mp hsum
      x (Finset.mem_univ x)
    exact sq_eq_zero_iff.mp (by simpa only [ite_eq_right hx] using h)
  constructor
  · intro x hx
    by_cases hy : x ∈ D
    · exact hDC x hy
    · exact hz x (by simp [hx, hy])
  · intro x hx
    by_cases hy : x ∈ C
    · exact hCD x hy
    · have hout' : x ∉ C ∪ D := by simp [hx, hy]
      have h := hneg x hout'
      rwa [hz x hout', zero_add] at h

private abbrev Rows (S : Finset (Q 9)) (b : Bool) := Interior S (!b)

private def extendRows (S : Finset (Q 9)) (b : Bool) : (Rows S b → ℝ) →ₗ[ℝ] Vec :=
  LinearMap.pi fun x =>
    if hx : parity x ≠ !b ∧ x ∈ S then LinearMap.proj ⟨⟨x, hx.1⟩, hx.2⟩ else 0

private theorem extendRows_apply {S : Finset (Q 9)} {b : Bool} (u : Rows S b → ℝ) (x : Q 9) :
    extendRows S b u x = if hx : parity x ≠ !b ∧ x ∈ S then u ⟨⟨x, hx.1⟩, hx.2⟩ else 0 := by
  simp only [extendRows, LinearMap.pi_apply]
  split_ifs <;> rfl

private theorem extendRows_injective (S : Finset (Q 9)) (b : Bool) :
    Function.Injective (extendRows S b) := by
  intro u v h
  funext x
  simpa [extendRows_apply, x.1.property, x.property] using congrFun h x.1.1

private def exteriorPart (S : Finset (Q 9)) (b : Bool) : Vec →ₗ[ℝ] (Exterior S b → ℝ) :=
  LinearMap.pi fun x => LinearMap.proj x.1.1

private theorem union_cubic {C D : Finset (Q 9)} (hsep : Separated C D)
    (hC : Cubic C) (hD : Cubic D) : Cubic (C ∪ D) := by
  intro x
  rcases Finset.mem_union.mp x.property with hx | hx
  · exact (degree_of_no_exterior_neighbors C (C ∪ D) (fun _ h => Finset.mem_union_left _ h)
      ⟨x.1, hx⟩ (fun y hy ha => (Finset.mem_union.mp hy).resolve_right
        (fun hyD => hsep _ hx y hyD ha))).trans (hC ⟨x.1, hx⟩)
  · exact (degree_of_no_exterior_neighbors D (C ∪ D) (fun _ h => Finset.mem_union_right _ h)
      ⟨x.1, hx⟩ (fun y hy ha => (Finset.mem_union.mp hy).resolve_left
        (fun hyC => hsep y hyC _ hx ha.symm))).trans (hD ⟨x.1, hx⟩)

private theorem crossing_dimensions {S : Finset (Q 9)} (b : Bool)
    (hS : S.card = 258) (hr : Cubic S) :
    Fintype.card (Rows S b) = 129 ∧ Fintype.card (Exterior S b) = 127 := by
  have h (c : Bool) := regular_parity_card S c (d := 3) (by decide) hr
  constructor
  · rw [interior_card, Bool.not_not]
    have := h b
    omega
  · rw [Fintype.card_subtype_compl (fun y : {x : Q 9 // parity x ≠ b} => y.1 ∈ S),
      cube_opposite_card, interior_card]
    have := h (!b)
    omega

/-- Two missing crossing rows allow one evaluation and one functional to be appended.
The determinant carries singularity across the exceptional parameter. -/
private theorem square_augmentation {ρ η : Type*} [Fintype ρ] [Fintype η]
    (hρ : Fintype.card ρ = 129) (hη : Fintype.card η = 127)
    (F G : (ρ → ℝ) →ₗ[ℝ] (η → ℝ)) (ev L : (ρ → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ (t : ℝ), t ≠ 1 → ∀ u, (F + (t - 1) • G) u = 0 → L u = 0) :
    ∃ u, u ≠ 0 ∧ F u = 0 ∧ ev u = 0 ∧ L u = 0 := by
  classical
  let crossing (t : ℝ) := F + (t - 1) • G
  have hcard : Fintype.card ρ = Fintype.card (η ⊕ Bool) := by
    simp [hρ, hη]
  let e := Fintype.equivOfCardEq hcard
  let aug (t : ℝ) : (ρ → ℝ) →ₗ[ℝ] (ρ → ℝ) :=
    LinearMap.pi fun a => Sum.elim (fun y => (LinearMap.proj y).comp (crossing t))
      (fun last => if last then L else ev) (e a)
  let A (t : ℝ) : Matrix ρ ρ ℝ := LinearMap.toMatrix' (aug t)
  have happ (t : ℝ) (u : ρ → ℝ) : aug t u = 0 ↔ crossing t u = 0 ∧ ev u = 0 ∧ L u = 0 := by
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · funext y
        simpa [aug] using congrFun h (e.symm (Sum.inl y))
      · simpa [aug] using congrFun h (e.symm (Sum.inr false))
      · simpa [aug] using congrFun h (e.symm (Sum.inr true))
    · rintro ⟨hF, he, hL'⟩
      funext a
      rcases ha : e a with y | last
      · simp [aug, ha, hF]
      · cases last <;> simp [aug, ha, he, hL']
  have hsing (t : ℝ) (ht : t ≠ 1) : (A t).det = 0 := by
    have hnull : 2 ≤ Module.finrank ℝ (crossing t).ker := by
      have hk := (crossing t).finrank_range_add_finrank_ker
      have hrange := (crossing t).range.finrank_le
      rw [Module.finrank_pi, hρ] at hk
      rw [Module.finrank_pi, hη] at hrange
      omega
    let B := ev.comp (crossing t).ker.subtype
    have hne : LinearMap.ker B ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by
        simpa using Nat.lt_of_lt_of_le (by decide : 1 < 2) hnull)
    obtain ⟨v, hv, hne⟩ := (Submodule.ne_bot_iff B.ker).mp hne
    let u : ρ → ℝ := v
    have hf : crossing t u = 0 := LinearMap.mem_ker.mp v.property
    have he : ev u = 0 := LinearMap.mem_ker.mp hv
    have hAu : (A t) *ᵥ u = 0 := by
      rw [LinearMap.toMatrix'_mulVec]
      exact (happ t u).2 ⟨hf, he, hL t ht u hf⟩
    by_contra hn
    have hi := Matrix.mulVec_injective_iff_isUnit.mpr
      ((A t).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hn))
    exact hne (Subtype.ext (hi (hAu.trans (Matrix.mulVec_zero _).symm)))
  have hcont : Continuous A := by
    apply continuous_matrix
    intro a c
    simp only [A, LinearMap.toMatrix'_apply]
    rcases ha : e a with y | last
    · simp only [aug, LinearMap.pi_apply, ha, Sum.elim_inl,
        LinearMap.comp_apply, LinearMap.proj_apply, crossing, LinearMap.add_apply,
        LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    · simp only [aug, LinearMap.pi_apply, ha, Sum.elim_inr]
      exact continuous_const
  have hzero : (A 1).det = 0 := by
    have heq : Set.EqOn (fun t => (A t).det) (fun _ => (0 : ℝ)) ({1}ᶜ : Set ℝ) :=
      fun t ht => hsing t (by simpa using ht)
    exact heq.closure hcont.matrix_det continuous_const
      ((dense_compl_singleton (1 : ℝ)).closure_eq.symm ▸ Set.mem_univ _)
  have hn : ¬ Function.Injective (fun u => (A 1) *ᵥ u) := by
    intro hi
    have hu := (A 1).isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hi)
    simp [hzero] at hu
  obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hn
  have hker : aug 1 (u - v) = 0 := by
    rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec_sub, huv, sub_self]
  obtain ⟨hf, he, hl⟩ := (happ _ _).1 hker
  refine ⟨u - v, sub_ne_zero.mpr hne, ?_, he, hl⟩
  simpa [crossing] using hf

private def axisWeight (j : Fin 9) (t : ℝ) (k : Fin 9) : ℝ := if k = j then t else 1

private theorem axis_weight (j : Fin 9) (t : ℝ) (f : Vec) :
    weightedLinear (axisWeight j t) f = H f + (t - 1) • gamma j f := by
  classical
  rw [← unit_weight, weighted_sum, weighted_sum,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  rw [show (∑ k ∈ Finset.univ.erase j, axisWeight j t k • gamma k f) =
    ∑ k ∈ Finset.univ.erase j, (1 : ℝ) • gamma k f by
      apply Finset.sum_congr rfl
      intro k hk
      rw [axisWeight, ite_eq_right (Finset.ne_of_mem_erase hk)]]
  simp only [axisWeight, one_smul, sub_smul]
  abel

private theorem axis_annihilates {C D : Finset (Q 9)} (hdisj : Disjoint C D)
    (hsep : Separated C D) (hrC : Cubic C) {s : Vec} (hs : IsSwitching C s)
    (b : Bool) (i j : Fin 9) {t : ℝ} (ht : t ≠ 1) {g : Vec}
    (hg : Supported D g) (hHg : Supported D (weightedLinear (axisWeight j t) g)) :
    parityPart b (switchingVector C s) ⬝ᵥ gamma i (gamma j g) = 0 := by
  let f := parityPart b (switchingVector C s)
  have hfs (c : Bool) : Supported C (parityPart c (switchingVector C s)) := by
    intro x hx
    simp [parityPart_apply, switchingVector, hx]
  have hweighted : gamma i f ⬝ᵥ weightedLinear (axisWeight j t) g = 0 := by
    rw [gamma_selfAdjoint]
    exact gamma_separated hsep i (hfs b) hHg
  have hunit : gamma i f ⬝ᵥ H g = 0 := by
    have hsym : (huangMatrix 9).IsSymm :=
      Matrix.IsSymm.ext (fun x y => huangMatrix_symmetric y x)
    change gamma i f ⬝ᵥ (huangMatrix 9).mulVec g = 0
    rw [hsym.dotProduct_mulVec_comm, dotProduct_comm g]
    have ha : H (gamma i f) = (2 : ℝ) • f - gamma i (H f) :=
      eq_sub_of_add_eq (anticommutator i f)
    change H (gamma i f) ⬝ᵥ g = 0
    rw [ha, sub_dotProduct, smul_dotProduct, dot_disjoint hdisj (hfs b) hg,
      gamma_selfAdjoint, parity_eigen C s hrC hs b, smul_dotProduct,
      gamma_separated hsep i (hfs (!b)) hg]
    ring
  rw [axis_weight, dotProduct_add, hunit, dotProduct_smul, gamma_selfAdjoint, zero_add] at hweighted
  exact (mul_eq_zero.mp hweighted).resolve_left (sub_ne_zero.mpr ht)

/-- For each cube parity the total signed two-direction contact is zero.
The proof uses the 129-to-127 exterior crossing and a single root evaluation. -/
theorem signed_overlap_parity_zero (C D : Finset (Q 9)) (s r : Vec)
    (hC : C.card = 72) (hD : D.card = 186) (hdisj : Disjoint C D)
    (hsep : Separated C D) (hrC : Cubic C) (hrD : Cubic D)
    (hcC : Connected C) (hcD : Connected D)
    (hs : IsSwitching C s) (hr : IsSwitching D r)
    (b : Bool) (i j : Fin 9) :
    parityPart b (switchingVector C s) ⬝ᵥ
      gamma i (gamma j (parityPart b (switchingVector D r))) = 0 := by
  classical
  let S := C ∪ D
  have hS : S.card = 258 := by
    rw [Finset.card_union_of_disjoint hdisj, hC, hD]
  obtain ⟨hrows, hext⟩ := crossing_dimensions b hS (union_cubic hsep hrC hrD)
  have exists_root (T : Finset (Q 9)) (ht : 0 < T.card) (htreg : Cubic T) :
      ∃ x : Q 9, x ∈ T ∧ parity x = b := by
    have h := regular_parity_card T b (d := 3) (by decide) htreg
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (paritySide T b).card by omega)
    exact ⟨x.1, x.property, (Finset.mem_filter.mp hx).2⟩
  obtain ⟨c, hc, hcb⟩ := exists_root C (by omega) hrC
  obtain ⟨d, hd, hdb⟩ := exists_root D (by omega) hrD
  let E := extendRows S b
  let F := (exteriorPart S b).comp (H.comp E)
  let G := (exteriorPart S b).comp ((gamma j).comp E)
  let ev := (LinearMap.proj c).comp E
  let f := parityPart b (switchingVector C s)
  let g := parityPart b (switchingVector D r)
  let L := (dotProductBilin ℝ ℝ f).comp
    ((gamma i).comp ((gamma j).comp ((supportPart D).comp E)))
  have hL_apply (u : Rows S b → ℝ) : L u = f ⬝ᵥ gamma i (gamma j (supportPart D (E u))) := rfl
  have hsplit (u : Rows S b → ℝ) : supportPart C (E u) + supportPart D (E u) = E u := by
    funext x
    by_cases hx : x ∈ S
    · rcases Finset.mem_union.mp hx with hxC | hxD
      · have hn : x ∉ D := fun h => Finset.disjoint_left.mp hdisj hxC h
        simp [supportPart_apply, hxC, hn]
      · have hn : x ∉ C := fun h => Finset.disjoint_left.mp hdisj h hxD
        simp [supportPart_apply, hxD, hn]
    · have hf : E u x = 0 := by simp [E, extendRows_apply, hx]
      simp [supportPart_apply, hf]
  have hsupport (T : Finset (Q 9)) (u : Rows S b → ℝ) : Supported T (supportPart T (E u)) := by
    intro x hx
    simp [supportPart_apply, hx]
  have hparity (T : Finset (Q 9)) (u : Rows S b → ℝ) : OnParity b (supportPart T (E u)) := by
    intro x hx
    have h := opposite_eq hx
    simp [supportPart_apply, E, extendRows_apply, h]
  have hkernel (t : ℝ) (u : Rows S b → ℝ) (hu : (F + (t - 1) • G) u = 0) :
      Supported C (weightedLinear (axisWeight j t) (supportPart C (E u))) ∧
      Supported D (weightedLinear (axisWeight j t) (supportPart D (E u))) := by
    apply split_crossing hdisj hsep _ (hsupport C u) (hsupport D u)
    rw [hsplit]
    intro x hx
    by_cases hb : parity x = b
    · have hE : OnParity b (E u) := by
        intro y hy
        rw [extendRows_apply, dite_eq_right (fun h => h.1 (opposite_eq hy))]
      exact weighted_cross (axisWeight j t) hE x (by rw [hb]; cases b <;> decide)
    · have h := congrFun hu (⟨⟨x, hb⟩, hx⟩ : Exterior S b)
      rw [axis_weight]
      exact h
  obtain ⟨u, hne, hF, hev, hLu⟩ :=
    square_augmentation hrows hext F G ev L (fun t ht u hu =>
      axis_annihilates hdisj hsep hrC hs b i j ht (hsupport D u) (hkernel t u hu).2)
  have hunit := hkernel 1 u (by simpa using hF)
  have hCline := unit_line hrC hcC hs (hsupport C u) (hparity C u)
    (by simpa [axis_weight] using hunit.1) c hc hcb
  have hDline := unit_line hrD hcD hr (hsupport D u) (hparity D u)
    (by simpa [axis_weight] using hunit.2) d hd hdb
  have hev' : E u c = 0 := hev
  rw [supportPart_apply, ite_eq_left hc, hev', zero_mul, zero_smul] at hCline
  have hcoeff : supportPart D (E u) d * r d ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hDline
    have hu0 : E u = 0 := by rw [← hsplit u, hCline, hDline, add_zero]
    exact hne (extendRows_injective S b (hu0.trans (map_zero E).symm))
  rw [hL_apply, hDline, map_smul, map_smul, dotProduct_smul] at hLu
  exact (mul_eq_zero.mp hLu).resolve_left hcoeff

private def bitSign (b : Bool) : ℝ := if b then -1 else 1

private theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

private def mask (i j : Fin 9) (a c : Bool) (x : Q 9) : ℝ :=
  bitSign (a && x i) * bitSign (c && x j)

private def maskWeight (i j : Fin 9) (a c : Bool) (k : Fin 9) : ℝ :=
  bitSign (a && decide (k = i)) * bitSign (c && decide (k = j))

private theorem mask_flip (i j k : Fin 9) (a c : Bool) (x : Q 9) :
    mask i j a c (flip x k) = maskWeight i j a c k * mask i j a c x := by
  have hbit (l : Fin 9) (flag : Bool) :
      bitSign (flag && flip x k l) =
        bitSign (flag && decide (k = l)) * bitSign (flag && x l) := by
    by_cases h : k = l
    · subst l
      cases flag <;> cases hx : x k <;>
        norm_num [bitSign, BalancedCriticalSpectrum.flip, hx]
    · cases flag <;> simp [bitSign, BalancedCriticalSpectrum.flip, h, Ne.symm h]
  simp only [mask, maskWeight, hbit]
  ring

private theorem mask_eigen (i j : Fin 9) (a c : Bool) (f : Vec) :
    weightedLinear (maskWeight i j a c) (fun x => mask i j a c x * f x) =
      fun x => mask i j a c x * H f x := by
  funext x
  rw [← unit_weight f]
  simp only [weighted_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gamma_apply,
    one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mask_flip]
  have hsq : maskWeight i j a c k ^ 2 = 1 := by
    simp only [maskWeight, mul_pow, bitSign_sq, mul_one]
  calc
    _ = maskWeight i j a c k ^ 2 *
        (mask i j a c x * (huangMatrix 9 x (flip x k) * f (flip x k))) := by ring
    _ = _ := by rw [hsq, one_mul]

private theorem weighted_anticommutator (w : Fin 9 → ℝ) (k : Fin 9) (f : Vec) :
    weightedLinear w (gamma k f) + gamma k (weightedLinear w f) = (2 * w k) • f := by
  simp only [weighted_sum, map_sum, map_smul, ← Finset.sum_add_distrib, ← smul_add]
  rw [Finset.sum_eq_single k]
  · rw [gamma_square, ← two_smul ℝ f, smul_smul, mul_comm]
  · intro l _ hl
    rw [gamma_anticommute hl f, neg_add_cancel, smul_zero]
  · simp

private theorem weight_difference {i j : Fin 9} (hij : i ≠ j) (a c : Bool) (g : Vec) :
    H g - weightedLinear (maskWeight i j a c) g =
      (1 - bitSign a) • gamma i g + (1 - bitSign c) • gamma j g := by
  rw [← unit_weight, weighted_sum, weighted_sum, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  rw [← Finset.sum_subset (s₁ := {i, j}) (Finset.subset_univ _) (by
    intro k _ hk
    have hi : k ≠ i := fun h => hk (by simp [h])
    have hj : k ≠ j := fun h => hk (by simp [h])
    simp [maskWeight, hi, hj, bitSign])]
  cases a <;> cases c <;> simp [Finset.sum_pair hij, maskWeight, bitSign, hij, hij.symm]

private theorem mask_overlap_zero {C D : Finset (Q 9)} (hdisj : Disjoint C D)
    (hsep : Separated C D) (hrC : Cubic C) (hrD : Cubic D)
    {s r : Vec} (hs : IsSwitching C s) (hr : IsSwitching D r)
    (b : Bool) {i j : Fin 9} (hij : i ≠ j) (a c : Bool) (hm : a = true ∨ c = true) :
    (fun x => mask i j a c x * parityPart b (switchingVector C s) x) ⬝ᵥ
      gamma i (gamma j (parityPart b (switchingVector D r))) = 0 := by
  let w := maskWeight i j a c
  let f := fun x => mask i j a c x * parityPart b (switchingVector C s) x
  let g := parityPart b (switchingVector D r)
  have hf : Supported C f := by
    intro x hx
    simp [f, parityPart_apply, switchingVector, hx]
  have hg : Supported D g := by
    intro x hx
    simp [g, parityPart_apply, switchingVector, hx]
  have hHf : Supported C (weightedLinear w f) := by
    rw [mask_eigen, parity_eigen C s hrC hs b]
    intro x hx
    simp [parityPart_apply, switchingVector, hx]
  have hHg : Supported D (H g) := by
    rw [parity_eigen D r hrD hr b]
    intro x hx
    simp [parityPart_apply, switchingVector, hx]
  have hdifference (k : Fin 9) :
      gamma k f ⬝ᵥ (H g - weightedLinear w g) = 0 := by
    have h1 : gamma k f ⬝ᵥ H g = 0 := by
      rw [gamma_selfAdjoint]
      exact gamma_separated hsep k hf hHg
    have h2 : gamma k f ⬝ᵥ weightedLinear w g = 0 := by
      rw [← weighted_selfAdjoint]
      have hanti : weightedLinear w (gamma k f) = (2 * w k) • f - gamma k (weightedLinear w f) :=
        eq_sub_of_add_eq (weighted_anticommutator w k f)
      rw [hanti, sub_dotProduct, smul_dotProduct, dot_disjoint hdisj hf hg,
        gamma_selfAdjoint, gamma_separated hsep k hHf hg]
      ring
    rw [dotProduct_sub, h1, h2, sub_zero]
  have hdiag (k : Fin 9) : f ⬝ᵥ gamma k (gamma k g) = 0 := by
    rw [gamma_square, dot_disjoint hdisj hf hg]
  change f ⬝ᵥ gamma i (gamma j g) = 0
  rcases Bool.eq_false_or_eq_true c with hc | hc
  swap
  · have ha := hm.resolve_right (by simp [hc])
    have hh := hdifference j
    change gamma j f ⬝ᵥ (H g - weightedLinear (maskWeight i j a c) g) = 0 at hh
    rw [weight_difference hij, dotProduct_add, dotProduct_smul, dotProduct_smul,
      gamma_selfAdjoint j f, gamma_selfAdjoint j f,
      gamma_anticommute hij.symm, dotProduct_neg, hdiag] at hh
    simp [ha, hc, bitSign] at hh
    linarith
  · have hh := hdifference i
    change gamma i f ⬝ᵥ (H g - weightedLinear (maskWeight i j a c) g) = 0 at hh
    rw [weight_difference hij, dotProduct_add, dotProduct_smul, dotProduct_smul,
      gamma_selfAdjoint i f, gamma_selfAdjoint i f, hdiag] at hh
    simp [hc, bitSign] at hh
    linarith

/-- For each parity and each prescribed pair of C-side bits, the signed
two-direction contact sum between the separated switches vanishes. -/
theorem signed_overlap_cell_zero (C D : Finset (Q 9)) (s r : Vec)
    (hC : C.card = 72) (hD : D.card = 186) (hdisj : Disjoint C D)
    (hsep : Separated C D) (hrC : Cubic C) (hrD : Cubic D)
    (hcC : Connected C) (hcD : Connected D)
    (hs : IsSwitching C s) (hr : IsSwitching D r)
    (b : Bool) (i j : Fin 9) (hij : i ≠ j) (p q : Bool) :
    (∑ x : Q 9, if x i = p ∧ x j = q then
      parityPart b (switchingVector C s) x *
        gamma i (gamma j (parityPart b (switchingVector D r))) x else 0) = 0 := by
  let f := parityPart b (switchingVector C s)
  let g := gamma i (gamma j (parityPart b (switchingVector D r)))
  have h00 : ∑ x, f x * g x = 0 :=
    signed_overlap_parity_zero C D s r hC hD hdisj hsep hrC hrD hcC hcD hs hr b i j
  have h10 : ∑ x, (bitSign (x i) * f x) * g x = 0 := by
    simpa [dotProduct, mask, bitSign] using
      mask_overlap_zero hdisj hsep hrC hrD hs hr b hij true false (Or.inl rfl)
  have h01 : ∑ x, (bitSign (x j) * f x) * g x = 0 := by
    simpa [dotProduct, mask, bitSign] using
      mask_overlap_zero hdisj hsep hrC hrD hs hr b hij false true (Or.inr rfl)
  have h11 : ∑ x, (bitSign (x i) * bitSign (x j) * f x) * g x = 0 := by
    simpa [dotProduct, mask] using
      mask_overlap_zero hdisj hsep hrC hrD hs hr b hij true true (Or.inl rfl)
  change (∑ x, if x i = p ∧ x j = q then f x * g x else 0) = 0
  have hindicator (x : Q 9) :
      4 * (if x i = p ∧ x j = q then f x * g x else 0) =
        f x * g x + bitSign p * ((bitSign (x i) * f x) * g x) +
          bitSign q * ((bitSign (x j) * f x) * g x) +
            (bitSign p * bitSign q) * ((bitSign (x i) * bitSign (x j) * f x) * g x) := by
    cases p <;> cases q <;> cases hxi : x i <;> cases hxj : x j <;>
      norm_num [hxi, hxj, bitSign] <;> ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hindicator x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h00, h10, h01, h11,
    mul_zero, add_zero] at hsum
  linarith

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells.signed_overlap_parity_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms signed_overlap_parity_zero
/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells.signed_overlap_cell_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms signed_overlap_cell_zero

end

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
