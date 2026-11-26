/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The weighted difference of two center-outward Huang differentials has exact energy. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-! Weighted outward differentials for the actual Huang signing of the Boolean cube.
The difference energy is the squared weighted distance between the centers times the
input energy. The identity controls the separation of kernels of the differentials
by the squared weights on the directions separating their centers.
The application is to Hong–Wu–Xia, arXiv:2610.09483v1, Section 7, Problem 2. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardDifference

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip_apply_same gamma gamma_apply)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeGirth (flip_comm)
open private edge edge_sq edge_reciprocal edge_curvature from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-- The weighted outward Huang differential centered at `c`. At the output vertex
`x`, coordinate `i` contributes exactly when its bit differs from the center's bit. -/
def outward {n : ℕ} (w : Fin n → ℝ) (c : Q n) (z : Q n → ℝ) (x : Q n) : ℝ :=
  ∑ i, w i * (if x i ≠ c i then gamma i z x else 0)

private def away (c b : Bool) : ℝ := if b ≠ c then 1 else 0

private def maskDifference (c d b : Bool) : ℝ := away c b - away d b

private theorem maskDifference_not (c d b : Bool) :
    maskDifference c d (!b) = -maskDifference c d b := by
  cases c <;> cases d <;> cases b <;> norm_num [maskDifference, away]

private theorem maskDifference_sq (c d b : Bool) :
    maskDifference c d b ^ 2 = if c ≠ d then 1 else 0 := by
  cases c <;> cases d <;> cases b <;> norm_num [maskDifference, away]

private def signedFlip {n : ℕ} (a : Bool → ℝ) (i : Fin n) (z : Q n → ℝ) (x : Q n) : ℝ :=
  a (x i) * (edge x i * z (flip x i))

private theorem outward_eq_sum {n : ℕ} (w : Fin n → ℝ) (c : Q n) (z : Q n → ℝ)
    (x : Q n) : outward w c z x = ∑ i, w i * signedFlip (away (c i)) i z x := by
  unfold outward
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : x i ≠ c i <;> simp [away, signedFlip, gamma_apply, h, edge]

private theorem outward_sub_eq_sum {n : ℕ} (w : Fin n → ℝ) (c d : Q n) (z : Q n → ℝ)
    (x : Q n) : outward w c z x - outward w d z x =
      ∑ i, w i * signedFlip (maskDifference (c i) (d i)) i z x := by
  rw [outward_eq_sum, outward_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [signedFlip, maskDifference]
  ring

private theorem flip_apply_of_ne {n : ℕ} (x : Q n) {i j : Fin n} (h : j ≠ i) :
    flip x i j = x j :=
  Function.update_of_ne h _ _

private theorem sum_flip {n : ℕ} (i : Fin n) (f : Q n → ℝ) :
    (∑ x, f (flip x i)) = ∑ x, f x := by
  let e : Q n ≃ Q n := ⟨(flip · i), (flip · i),
    fun x => BalancedCriticalSpectrum.flip_flip x i,
    fun x => BalancedCriticalSpectrum.flip_flip x i⟩
  exact Equiv.sum_comp e f

private theorem sum_signedFlip_sq {n : ℕ} (i : Fin n) (z : Q n → ℝ)
    {a : Bool → ℝ} {s : ℝ} (ha : ∀ b, a b ^ 2 = s) :
    (∑ x, signedFlip a i z x ^ 2) = s * (∑ x, z x ^ 2) := by
  calc
    (∑ x, signedFlip a i z x ^ 2) = ∑ x, s * z (flip x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [signedFlip, mul_pow, ha, edge_sq, one_mul]
    _ = s * (∑ x, z x ^ 2) := by
      rw [← Finset.mul_sum, sum_flip i (fun x => z x ^ 2)]

/-- On the opposite corner of a two-coordinate face, the two outgoing edge signs
have the opposite product by Huang square curvature and edge reciprocity. -/
private theorem double_flip_edge_product {n : ℕ} (x : Q n) {i j : Fin n} (hij : i ≠ j) :
    edge (flip (flip x i) j) i * edge (flip (flip x i) j) j = -(edge x i * edge x j) := by
  have h := edge_curvature (flip x i) hij
  rw [edge_reciprocal x i, BalancedCriticalSpectrum.flip_flip] at h
  calc
    _ = edge (flip x i) j * edge (flip (flip x i) j) i := by
      rw [edge_reciprocal (flip x i) j, mul_comm]
    _ = _ := by rw [h, neg_neg]

private theorem sum_signedFlip_mul_eq_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a b : Bool → ℝ) (ha : ∀ t, a (!t) = -a t) (hb : ∀ t, b (!t) = -b t)
    (z : Q n → ℝ) : (∑ x, signedFlip a i z x * signedFlip b j z x) = 0 := by
  let f (x : Q n) := signedFlip a i z x * signedFlip b j z x
  have hopposite (x : Q n) : f (flip (flip x i) j) = -f x := by
    let y := flip (flip x i) j
    have hyi : y i = !(x i) := by
      dsimp only [y]
      rw [flip_apply_of_ne (flip x i) hij, flip_apply_same]
    have hyj : y j = !(x j) := by
      dsimp only [y]
      rw [flip_apply_same, flip_apply_of_ne x hij.symm]
    have hyflip : flip y i = flip x j := by
      dsimp only [y]
      rw [flip_comm (flip x i) j i, BalancedCriticalSpectrum.flip_flip]
    change signedFlip a i z y * signedFlip b j z y =
      -(signedFlip a i z x * signedFlip b j z x)
    simp only [signedFlip, hyi, hyj, ha, hb, hyflip]
    rw [show flip y j = flip x i from BalancedCriticalSpectrum.flip_flip (flip x i) j]
    calc
      _ = (a (x i) * b (x j) * (z (flip x j) * z (flip x i))) *
          (edge y i * edge y j) := by ring
      _ = _ := by rw [show edge y i * edge y j = _ from double_flip_edge_product x hij]; ring
  have hsum : (∑ x, f x) = -(∑ x, f x) := calc
    (∑ x, f x) = ∑ x, f (flip x j) := (sum_flip j f).symm
    _ = ∑ x, f (flip (flip x i) j) := (sum_flip i (fun x => f (flip x j))).symm
    _ = -(∑ x, f x) := by simp only [hopposite, Finset.sum_neg_distrib]
  change (∑ x, f x) = 0
  linarith only [hsum]

/-- The energy of the difference of two outward differentials is exactly the input
energy times the sum of squared weights on the coordinates where the centers differ. -/
theorem outward_sub_energy {n : ℕ} (w : Fin n → ℝ) (c d : Q n) (z : Q n → ℝ) :
    (∑ x, (outward w c z x - outward w d z x) ^ 2) =
      (∑ i ∈ Finset.univ.filter (fun i => c i ≠ d i), w i ^ 2) * (∑ x, z x ^ 2) := by
  let a (i : Fin n) := maskDifference (c i) (d i)
  let term (i : Fin n) (x : Q n) := w i * signedFlip (a i) i z x
  have hfactor (i j : Fin n) : (∑ x, term i x * term j x) =
      (w i * w j) * (∑ x, signedFlip (a i) i z x * signedFlip (a j) j z x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [term]
    ring
  calc
    _ = ∑ x, (∑ i, term i x) ^ 2 := by simp only [outward_sub_eq_sum, term, a]
    _ = ∑ x, ∑ i, ∑ j, term i x * term j x := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ x, term i x * term j x := calc
      _ = ∑ i, ∑ x, ∑ j, term i x * term j x := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i : Fin n, (if c i ≠ d i then w i ^ 2 else 0) * (∑ x, z x ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [hfactor]
        simp only [← pow_two]
        rw [sum_signedFlip_sq i z (a := a i) (maskDifference_sq (c i) (d i))]
        by_cases h : c i ≠ d i <;> simp [h]
      · intro j _ hji
        rw [hfactor, sum_signedFlip_mul_eq_zero hji.symm (a i) (a j)
          (maskDifference_not (c i) (d i)) (maskDifference_not (c j) (d j)) z, mul_zero]
      · simp
    _ = _ := by rw [← Finset.sum_mul, Finset.sum_filter]

private theorem signedFlip_anticommute {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a b : Bool → ℝ) (z : Q n → ℝ) (x : Q n) :
    signedFlip a i (signedFlip b j z) x = -(signedFlip b j (signedFlip a i z) x) := by
  simp only [signedFlip, flip_apply_of_ne x hij, flip_apply_of_ne x hij.symm, flip_comm x i j]
  calc
    _ = (a (x i) * b (x j)) * (edge x i * edge (flip x i) j) * z (flip (flip x j) i) := by
      ring
    _ = _ := by rw [edge_curvature x hij]; ring

private theorem signedFlip_away_sq {n : ℕ} (c : Q n) (i : Fin n) (z : Q n → ℝ) (x : Q n) :
    signedFlip (away (c i)) i (signedFlip (away (c i)) i z) x = 0 := by
  have hmask (b t : Bool) : away b t * away b (!t) = 0 := by
    cases b <;> cases t <;> norm_num [away]
  simp only [signedFlip, flip_apply_same, BalancedCriticalSpectrum.flip_flip]
  calc
    _ = (away (c i) (x i) * away (c i) (!(x i))) *
        (edge x i * edge (flip x i) i) * z x := by ring
    _ = 0 := by rw [hmask, zero_mul, zero_mul]

/-- The weighted outward Huang differential squares to zero at each center. -/
theorem outward_sq {n : ℕ} (w : Fin n → ℝ) (c : Q n) (z : Q n → ℝ) :
    outward w c (outward w c z) = 0 := by
  funext x
  change outward w c (outward w c z) x = 0
  let f (i j : Fin n) := w i * w j *
    signedFlip (away (c i)) i (signedFlip (away (c j)) j z) x
  have hterm (i j : Fin n) : f i j = -f j i := by
    dsimp only [f]
    by_cases hij : i = j
    · subst j
      simp only [signedFlip_away_sq, mul_zero, neg_zero]
    · rw [signedFlip_anticommute hij]
      ring
  have hsum : (∑ i, ∑ j, f i j) = -(∑ i, ∑ j, f i j) := calc
    _ = ∑ i, ∑ j, -f j i :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = _ := by
      simp only [Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
  calc
    _ = ∑ i, ∑ j, f i j := by
      simp only [outward_eq_sum, signedFlip, Finset.mul_sum, f]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by linarith only [hsum]

/-- If three closed centered residuals cancel, each pair of weighted center
distances determines the ratio of the other two residual energies. Applying the
first center's differential to the cancellation gives the exact relation. -/
theorem closed_triple_energy_relation {n : ℕ} (w : Fin n → ℝ)
    (a b c : Q n) (x y z : Q n → ℝ)
    (hx : outward w a x = 0) (hy : outward w b y = 0) (hz : outward w c z = 0)
    (hcancel : x + y + z = 0) :
    (∑ i ∈ Finset.univ.filter (fun i => a i ≠ b i), w i ^ 2) * (∑ r, y r ^ 2) =
      (∑ i ∈ Finset.univ.filter (fun i => a i ≠ c i), w i ^ 2) * (∑ r, z r ^ 2) := by
  classical
  have hrow (r : Q n) : outward w a y r = -outward w a z r := by
    have hadd : outward w a (x + y + z) r =
        outward w a x r + outward w a y r + outward w a z r := by
      simp only [outward, map_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : r i ≠ a i <;> simp [h] <;> ring
    rw [hcancel, hx] at hadd
    simp only [outward, map_zero, Pi.zero_apply, ite_self, mul_zero, Finset.sum_const_zero,
      zero_add] at hadd
    change 0 = outward w a y r + outward w a z r at hadd
    linarith only [hadd]
  calc
    _ = ∑ r, (outward w a y r - outward w b y r) ^ 2 :=
      (outward_sub_energy w a b y).symm
    _ = ∑ r, (outward w a z r - outward w c z r) ^ 2 := by
      rw [hy, hz]
      apply Finset.sum_congr rfl
      intro r _
      simp [hrow r]
    _ = _ := outward_sub_energy w a c z

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardDifference
