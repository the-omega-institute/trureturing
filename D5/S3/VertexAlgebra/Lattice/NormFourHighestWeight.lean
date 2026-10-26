/- GID: D5/S3/VertexAlgebra/Lattice/NormFourHighestWeight
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourHighestWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual norm-four vacuum null field restricts all highest-weight eigenvalues. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull

/-! Highest-weight restrictions from the actual lattice null state and state-field calculus.
The norm-four vector retains its Dong-Mason-Zhu / Shimakura attribution, and
imported lattice and residue calculus retain their Bakalov-Kac and Carnahan /
Matsuo-Nagatomo attribution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.Lattice.NormFourHighestWeight

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeActualStateFieldCalculus LatticeActualStateDerivative
open NormFourVirasoroVector
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator

noncomputable section

/-- Linearity in the actual argument of a field coefficient. -/
private theorem product_smul_right (D : LatticeData) (v u : Carrier D)
    (n : ℤ) (c : ℂ) : mu D v n (c • u) = c • mu D v n u := by
  exact map_smul ((Y D v)[[n]]) c u

/-- Actual vacuum data, with degree zero and top coefficient one. -/
private theorem vacuum_data (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : Carrier D) :
    mode D a s (-1) (vacuum D) = translation D (vacuum D) ∧
    (∀ n : ℤ, 0 ≤ n → mu D (vacuum D) n w = 0) ∧
    mu D (vacuum D) (-1) w = (1 : ℂ) • w := by
  refine ⟨?_, ?_, ?_⟩
  · rw [translation_kills_vacuum]
    change ((Y D (vector D a s))[[0]]) (vacuum D) = 0
    exact stateField_creativity D (vector D a s) 0 (by omega)
  · intro n hn
    simp [mu, stateField_vacuum, identity_modes, show n ≠ -1 by omega]
  · simp [mu, stateField_vacuum, identity_modes]

/-- Propagate axis L_{-1}=T using the actual two commutators. -/
private theorem translation_step (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (v : Carrier D) (k : ℤ) (hk : 2 ≤ k)
    (hv : mode D a s (-1) v = translation D v) :
    mode D a s (-1) (mode D a s (-k) v) =
      translation D (mode D a s (-k) v) := by
  have notCentral : (-1 : ℤ) + -k ≠ 0 := by omega
  have axisOp := virasoro_commutator D a ha s hs (-1) (-k)
  rw [if_neg notCentral, add_zero] at axisOp
  have axis := congrArg (fun A : Module.End ℂ (Carrier D) => A v) axisOp
  change mode D a s (-1) (mode D a s (-k) v) -
      mode D a s (-k) (mode D a s (-1) v) =
        (((-1 : ℤ) : ℂ) - ((-k : ℤ) : ℂ)) •
          mode D a s (-1 + -k) v at axis
  rw [show (-1 : ℤ) + -k = -k - 1 by omega] at axis
  rw [hv] at axis
  have ambient := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
    (stateField_covariance D (vector D a s) (-k + 1))
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at ambient
  rw [show -k + 1 - 1 = (-k - 1) + 1 by omega] at ambient
  change translation D (mode D a s (-k) v) -
      mode D a s (-k) (translation D v) =
        -((-k + 1 : ℤ) : ℂ) • mode D a s (-k - 1) v at ambient
  have scalar : ((-1 : ℤ) : ℂ) - ((-k : ℤ) : ℂ) =
      -((-k + 1 : ℤ) : ℂ) := by
    push_cast
    ring
  rw [scalar] at axis
  have cancellation := congrArg
    (fun x : Carrier D => x + mode D a s (-k) (translation D v))
    (axis.trans ambient.symm)
  simpa only [sub_add_cancel] using cancellation

/-- A zero-mode commutator extracted with support exactly {0}.
All q are integers; the equality with T is a proved descendant input. -/
private theorem coefficient_axis_commute (D : LatticeData) (a : Charge D)
    (s : ℂ) (v : Carrier D)
    (hv : mode D a s (-1) v = translation D v) (q : ℤ) (w : Carrier D) :
    mu D v q (mode D a s (-1) w) =
      mode D a s (-1) (mu D v q w) + (q : ℂ) • mu D v (q - 1) w := by
  classical
  have singleton : (∑ᶠ j : ℕ,
      commutatorTerm D (vector D a s) v 0 q j) =
        ((Y D (mu D (vector D a s) 0 v))[[q]]) := by
    rw [finsum_eq_single _ 0]
    · simp [commutatorTerm, integerBinomial]
    · intro j hj
      simp [commutatorTerm, integerBinomial,
        Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  have comm := mode_commutator D (vector D a s) v 0 q
  rw [singleton] at comm
  have state : mu D (vector D a s) 0 v = translation D v := hv
  rw [state, state_derivative_modes] at comm
  have evaluated := congrArg (fun A : Module.End ℂ (Carrier D) => A w) comm
  change mode D a s (-1) (mu D v q w) -
      mu D v q (mode D a s (-1) w) =
        -(q : ℂ) • mu D v (q - 1) w at evaluated
  calc
    mu D v q (mode D a s (-1) w) =
        mode D a s (-1) (mu D v q w) -
          (mode D a s (-1) (mu D v q w) -
            mu D v q (mode D a s (-1) w)) := by abel
    _ = _ := by rw [evaluated, neg_smul, sub_neg_eq_add]

/-- Full-iterate reduction, including every natural offset and
every integer n above the top boundary. No descendant vanishing is assumed
except for the strictly shorter v, and all offsets at least two vanish by
the actual highest-weight hypothesis itself. -/
private theorem iterate_two_terms (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : Carrier D)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0)
    (v : Carrier D) (d k n : ℤ) (hk : 2 ≤ k)
    (high : ∀ q : ℤ, d ≤ q → mu D v q w = 0)
    (hn : d + k - 1 ≤ n) :
    mu D (mode D a s (-k) v) n w =
      -((-1 : ℂ) ^ (1 - k)) •
        (mu D v (n + 1 - k) (mode D a s (-1) w) +
          ((k : ℂ) - 1) • mu D v (n - k) (mode D a s 0 w)) := by
  classical
  let weight (j : ℕ) : ℂ :=
    (-1 : ℂ) ^ j * ((Ring.choose (1 - k) j : ℤ) : ℂ)
  let left (j : ℕ) : Carrier D :=
    weight j • mu D (vector D a s) (1 - k - j) (mu D v (n + j) w)
  let right (j : ℕ) : Carrier D :=
    weight j • mu D v (1 - k + n - j) (mu D (vector D a s) j w)
  have actual := stateField_iterate D (vector D a s) v w (1 - k) n
  have identity := actual.2.2
  change mu D (mu D (vector D a s) (1 - k) v) n w =
    (∑ᶠ j : ℕ, left j) - ((-1 : ℂ) ^ (1 - k)) •
      (∑ᶠ j : ℕ, right j) at identity
  have descendant : mu D (vector D a s) (1 - k) v =
      mode D a s (-k) v := by
    rw [show 1 - k = -k + 1 by omega]
    rfl
  rw [descendant] at identity
  have leftZero : (∑ᶠ j : ℕ, left j) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    dsimp only [left]
    rw [high (n + j) (by omega)]
    simp only [mu, map_zero, smul_zero]
  have tail (j : ℕ) (hj : 2 ≤ j) : mu D (vector D a s) j w = 0 := by
    have kill := positive ((j : ℤ) - 1) (by omega)
    simpa only [mode, mu, show (j : ℤ) - 1 + 1 = j by omega] using kill
  have rightFinite : (∑ᶠ j : ℕ, right j) =
      ∑ j ∈ Finset.range 2, right j := by
    apply finsum_eq_sum_of_support_subset
    intro j member
    apply Finset.mem_range.mpr
    by_contra outside
    have hj : 2 ≤ j := by omega
    exact member (by
      dsimp only [right]
      rw [tail j hj]
      simp only [mu, map_zero, smul_zero])
  have weight0 : weight 0 = 1 := by simp [weight]
  have weight1 : weight 1 = (k : ℂ) - 1 := by
    dsimp only [weight]
    norm_num only [pow_one, Ring.choose_one_right]
    push_cast
    ring
  have right0 : right 0 = mu D v (n + 1 - k) (mode D a s (-1) w) := by
    simp only [right, weight0, Nat.cast_zero, sub_zero, one_smul,
      show 1 - k + n = n + 1 - k by omega]
    rfl
  have right1 : right 1 =
      ((k : ℂ) - 1) • mu D v (n - k) (mode D a s 0 w) := by
    simp only [right, weight1, Nat.cast_one,
      show 1 - k + n - 1 = n - k by omega]
    rfl
  have rightSum : (∑ᶠ j : ℕ, right j) =
      mu D v (n + 1 - k) (mode D a s (-1) w) +
        ((k : ℂ) - 1) • mu D v (n - k) (mode D a s 0 w) := by
    rw [rightFinite]
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [right0, right1]
  rw [leftZero, rightSum] at identity
  simpa only [zero_sub, neg_smul] using identity

/-- All positive-degree modes of the next actual descendant.
Both q and q-1 in the L_{-1} term are covered, including the boundary n=d+k. -/
private theorem high_step (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : Carrier D) (h : ℂ) (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0)
    (v : Carrier D) (d k : ℤ) (hk : 2 ≤ k)
    (translated : mode D a s (-1) v = translation D v)
    (high : ∀ q : ℤ, d ≤ q → mu D v q w = 0) :
    ∀ n : ℤ, d + k ≤ n → mu D (mode D a s (-k) v) n w = 0 := by
  intro n hn
  rw [iterate_two_terms D a s w positive v d k n hk high (by omega),
    coefficient_axis_commute D a s v translated (n + 1 - k) w,
    high (n + 1 - k) (by omega), map_zero,
    high (n + 1 - k - 1) (by omega), smul_zero, zero_add,
    zeroMode, product_smul_right,
    high (n - k) (by omega)]
  simp only [smul_zero, add_zero]

/-- Actual top coefficient recursion, proved rather than posited:
the multiplier for L_{-k} is (-1)^k(d+(k-1)h). The displayed zpow form avoids
any restriction on the parity of the arbitrary integer k at least two. -/
private theorem top_step (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : Carrier D) (h : ℂ) (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0)
    (v : Carrier D) (d k : ℤ) (hk : 2 ≤ k) (c : ℂ)
    (translated : mode D a s (-1) v = translation D v)
    (high : ∀ q : ℤ, d ≤ q → mu D v q w = 0)
    (top : mu D v (d - 1) w = c • w) :
    mu D (mode D a s (-k) v) (d + k - 1) w =
      (-((-1 : ℂ) ^ (1 - k)) *
        ((d : ℂ) + ((k : ℂ) - 1) * h) * c) • w := by
  rw [iterate_two_terms D a s w positive v d k (d + k - 1) hk high (by omega),
    show d + k - 1 + 1 - k = d by omega,
    show d + k - 1 - k = d - 1 by omega,
    coefficient_axis_commute D a s v translated d w,
    high d le_rfl, map_zero, zero_add,
    zeroMode, product_smul_right]
  simp only [top]
  module

/-- Data propagation only for the actual descendants consumed below. -/
private theorem descendant_step (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (w : Carrier D) (h : ℂ) (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0)
    (v : Carrier D) (d k : ℤ) (hk : 2 ≤ k) (c : ℂ)
    (translated : mode D a s (-1) v = translation D v)
    (high : ∀ q : ℤ, d ≤ q → mu D v q w = 0)
    (top : mu D v (d - 1) w = c • w) :
    mode D a s (-1) (mode D a s (-k) v) =
        translation D (mode D a s (-k) v) ∧
    (∀ q : ℤ, d + k ≤ q → mu D (mode D a s (-k) v) q w = 0) ∧
    mu D (mode D a s (-k) v) (d + k - 1) w =
      (-((-1 : ℂ) ^ (1 - k)) *
        ((d : ℂ) + ((k : ℂ) - 1) * h) * c) • w :=
  ⟨translation_step D a ha s hs v k hk translated,
    high_step D a s w h zeroMode positive v d k hk translated high,
    top_step D a s w h zeroMode positive v d k hk c translated high top⟩

/-- Shared degree-two descendant data, all derived from the vacuum. -/
private theorem weight_two_data (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (w : Carrier D) (h : ℂ) (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0) :
    mode D a s (-1) (mode D a s (-2) (vacuum D)) =
        translation D (mode D a s (-2) (vacuum D)) ∧
    (∀ q : ℤ, 2 ≤ q → mu D (mode D a s (-2) (vacuum D)) q w = 0) ∧
    mu D (mode D a s (-2) (vacuum D)) 1 w = h • w := by
  obtain ⟨t, z, o⟩ := vacuum_data D a s w
  have step := descendant_step D a ha s hs w h zeroMode positive
    (vacuum D) 0 2 (by omega) 1 t z o
  norm_num at step
  exact step

/-- The first of the four actual level-six images. -/
private theorem image_222 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (w : Carrier D) (h : ℂ) (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0) :
    mu D (mode D a s (-2) (mode D a s (-2)
      (mode D a s (-2) (vacuum D)))) 5 w = (h * (h + 2) * (h + 4)) • w := by
  obtain ⟨t2, z2, o2⟩ := weight_two_data D a ha s hs w h zeroMode positive
  obtain ⟨t4, z4, o4⟩ := descendant_step D a ha s hs w h zeroMode positive
    (mode D a s (-2) (vacuum D)) 2 2 (by omega) h t2 z2 o2
  have o4' : mu D (mode D a s (-2) (mode D a s (-2) (vacuum D)))
      (4 - 1) w = ((h + 2) * h) • w := by
    convert o4 using 1 <;> norm_num <;> module
  have last := top_step D a s w h zeroMode positive
    (mode D a s (-2) (mode D a s (-2) (vacuum D))) 4 2 (by omega)
    ((h + 2) * h) t4 z4 o4'
  convert last using 1 <;> norm_num <;> module

/-- The second actual level-six image, including both odd signs. -/
private theorem image_33 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (w : Carrier D) (h : ℂ) (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0) :
    mu D (mode D a s (-3) (mode D a s (-3) (vacuum D))) 5 w =
      (2 * h * (2 * h + 3)) • w := by
  obtain ⟨t0, z0, o0⟩ := vacuum_data D a s w
  obtain ⟨t3, z3, o3⟩ := descendant_step D a ha s hs w h zeroMode positive
    (vacuum D) 0 3 (by omega) 1 t0 z0 o0
  have o3' : mu D (mode D a s (-3) (vacuum D)) (3 - 1) w =
      (-2 * h) • w := by
    convert o3 using 1 <;> norm_num <;> module
  have last := top_step D a s w h zeroMode positive
    (mode D a s (-3) (vacuum D)) 3 3 (by omega) (-2 * h) t3 z3 o3'
  convert last using 1 <;> norm_num <;> module

/-- The third actual level-six image. -/
private theorem image_42 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (w : Carrier D) (h : ℂ) (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0) :
    mu D (mode D a s (-4) (mode D a s (-2) (vacuum D))) 5 w =
      (h * (3 * h + 2)) • w := by
  obtain ⟨t2, z2, o2⟩ := weight_two_data D a ha s hs w h zeroMode positive
  have last := top_step D a s w h zeroMode positive
    (mode D a s (-2) (vacuum D)) 2 4 (by omega) h t2 z2 o2
  convert last using 1 <;> norm_num <;> module

/-- The fourth actual level-six image. -/
private theorem image_6 (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : Carrier D) (h : ℂ) (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0) :
    mu D (mode D a s (-6) (vacuum D)) 5 w = (5 * h) • w := by
  obtain ⟨t0, z0, o0⟩ := vacuum_data D a s w
  have last := top_step D a s w h zeroMode positive
    (vacuum D) 0 6 (by omega) 1 t0 z0 o0
  convert last using 1 <;> norm_num <;> module

/-- Highest-weight values of the ACTUAL norm-four lattice modes.
The actual null-state relation is a proved dependency.
No positivity, rootlessness, rank, determinant, simplicity, eigenbasis,
selected-subspace, assumed descendant recursion or assumed null state is used. -/
theorem highest_weight_values (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (h : ℂ) (w : Carrier D) (nonzero : w ≠ 0)
    (zeroMode : mode D a s 0 w = h • w)
    (positive : ∀ m : ℤ, 0 < m → mode D a s m w = 0) :
    h = 0 ∨ h = (1 / 16 : ℂ) ∨ h = (1 / 2 : ℂ) := by
  have nullAction := congrArg (fun v : Carrier D => mu D v 5 w)
    (NormFourVacuumNull.level_six_vacuum_null D a ha s hs)
  have linearAction :
      (64 : ℂ) • mu D (mode D a s (-2) (mode D a s (-2)
        (mode D a s (-2) (vacuum D)))) 5 w +
      (93 : ℂ) • mu D (mode D a s (-3) (mode D a s (-3) (vacuum D))) 5 w -
      (264 : ℂ) • mu D (mode D a s (-4) (mode D a s (-2) (vacuum D))) 5 w -
      (108 : ℂ) • mu D (mode D a s (-6) (vacuum D)) 5 w = 0 := by
    simpa only [mu, map_add, map_sub, map_smul, map_zero,
      VertexOperator.ncoeff, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Pi.zero_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.zero_apply] using nullAction
  rw [image_222 D a ha s hs w h zeroMode positive,
    image_33 D a ha s hs w h zeroMode positive,
    image_42 D a ha s hs w h zeroMode positive,
    image_6 D a s w h zeroMode positive] at linearAction
  have factoredAction :
      ((64 : ℂ) * (h * (h - 1 / 16) * (h - 1 / 2))) • w = 0 := by
    calc
      _ = (64 : ℂ) • ((h * (h + 2) * (h + 4)) • w) +
          (93 : ℂ) • ((2 * h * (2 * h + 3)) • w) -
          (264 : ℂ) • ((h * (3 * h + 2)) • w) -
          (108 : ℂ) • ((5 * h) • w) := by module
      _ = 0 := linearAction
  have scalar := (smul_eq_zero.mp factoredAction).resolve_right nonzero
  have roots : h * (h - 1 / 16) * (h - 1 / 2) = 0 :=
    (mul_eq_zero.mp scalar).resolve_left (by norm_num)
  rcases mul_eq_zero.mp roots with pair | half
  · rcases mul_eq_zero.mp pair with zero | sixteenth
    · exact Or.inl zero
    · exact Or.inr (Or.inl (sub_eq_zero.mp sixteenth))
  · exact Or.inr (Or.inr (sub_eq_zero.mp half))

end
end D5.S3.VertexAlgebra.Lattice.NormFourHighestWeight
