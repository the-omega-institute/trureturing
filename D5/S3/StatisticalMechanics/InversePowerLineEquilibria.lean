/- GID: D5/S3/StatisticalMechanics/InversePowerLineEquilibria
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/InversePowerLineEquilibria
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every absolutely convergent inverse-power equilibrium is affine for s>2. -/

/-
admission_basis: escape-witness
question_answered: https://github.com/the-omega-institute/trureturing/issues/27202
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27401
claim:
  proof_shape: bind-only; escape_witness: none.
  consumers: result.
energy_bound_by_supported_moments:
  proof_shape: content; escape_witness: energy_bound_by_supported_moments.
  consumers: capacity_zero_of_second_moment_mass_bound.
cutoff_lipschitz:
  proof_shape: bind-only; escape_witness: none.
  consumers: capacity_zero_of_second_moment_mass_bound.
cutoff_one:
  proof_shape: bind-only; escape_witness: none.
  consumers: capacity_zero_of_second_moment_mass_bound.
cutoff_zero:
  proof_shape: bind-only; escape_witness: none.
  consumers: capacity_zero_of_second_moment_mass_bound.
capacity_zero_of_second_moment_mass_bound:
  proof_shape: content; escape_witness: capacity_zero_of_second_moment_mass_bound.
  consumers: reciprocal_constant_of_power_bound.
reciprocal_constant_of_power_bound:
  proof_shape: content; escape_witness: capacity_zero_of_second_moment_mass_bound.
  consumers: equilibrium_is_progression.
equilibrium_is_progression:
  proof_shape: content; escape_witness: capacity_zero_of_second_moment_mass_bound.
  consumers: result.
result:
  proof_shape: content; escape_witness: capacity_zero_of_second_moment_mass_bound.
  consumers: terminal result.
-/

import D5.S3.StatisticalMechanics.InversePowerLineBasics
import D5.S3.StatisticalMechanics.InversePowerLineConductance
import D5.S3.StatisticalMechanics.InversePowerLineNetwork
import D5.S3.StatisticalMechanics.InversePowerLinePowerPacking


/-!
# Rigidity of inverse-power line equilibria for real exponents greater than two
-/

namespace D5.S3.StatisticalMechanics.InversePowerLineEquilibria

open D5.S3.StatisticalMechanics.InversePowerLineBasics
open D5.S3.StatisticalMechanics.InversePowerLineConductance
open D5.S3.StatisticalMechanics.InversePowerLineNetwork
open D5.S3.StatisticalMechanics.InversePowerLinePowerPacking

def claim : Prop :=
  ∀ s : ℝ, 2 < s →
    (∃ X : Set ℝ, IsSEquilibrium s X) ∧
    ∀ X : Set ℝ, IsSEquilibrium s X ↔
      ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, X = arithmeticProgression α β

private theorem energy_bound_by_supported_moments {V : Type*}
    (C : V → V → ℝ) (hsymm : ∀ x y, C x y = C y x)
    (hnonneg : ∀ x y, 0 ≤ C x y) (hrow : ∀ x, Summable (C x))
    (a f : V → ℝ) (S : Finset V) (hf : ∀ x, x ∉ S → f x = 0)
    (R : ℝ)
    (hLip : ∀ x y, (f x - f y)^2 ≤ (a x - a y)^2 / R^2)
    (hmoment : ∀ x, Summable (fun y => C x y * (a x - a y)^2)) :
    energy C f ≤ (∑ x ∈ S, ∑' y, C x y * (a x - a y)^2) / R^2 := by
  classical
  let L : V × V → ℝ := fun p =>
    if p.1 ∈ S then C p.1 p.2 * (a p.1 - a p.2)^2 / R^2 else 0
  have hL : Summable L := by
    apply summable_finite_rows S
    · intro x
      by_cases hx : x ∈ S
      · simpa [L, hx] using (hmoment x).div_const (R^2)
      · simp [L, hx]
    · intro x hx y
      simp [L, hx]
  have hLp (p : V × V) : 0 ≤ L p := by
    dsimp [L]
    split_ifs
    · exact div_nonneg (mul_nonneg (hnonneg _ _) (sq_nonneg _)) (sq_nonneg _)
    · exact le_rfl
  have he : Summable (fun p : V × V => C p.1 p.2 * (f p.1 - f p.2)^2) :=
    energy_summable C hsymm hnonneg hrow f S hf
  have hpoint (p : V × V) : C p.1 p.2 * (f p.1 - f p.2)^2 ≤ L p + L p.swap := by
    by_cases hx : p.1 ∈ S
    · have h : C p.1 p.2 * (f p.1 - f p.2)^2 ≤ L p := by
        dsimp [L]
        rw [ite_eq_left hx, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hLip _ _) (hnonneg _ _)
      exact h.trans (le_add_of_nonneg_right (hLp _))
    · by_cases hy : p.2 ∈ S
      · have h : C p.1 p.2 * (f p.1 - f p.2)^2 ≤ L p.swap := by
          dsimp [L]
          rw [ite_eq_left hy, hsymm p.2 p.1,
            show (a p.2 - a p.1)^2 = (a p.1 - a p.2)^2 by ring, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (hLip _ _) (hnonneg _ _)
        exact h.trans (le_add_of_nonneg_left (hLp _))
      · simp [hf _ hx, hf _ hy, L, hx, hy]
  have ht := he.tsum_le_tsum hpoint (hL.add hL.prod_symm)
  rw [hL.tsum_add hL.prod_symm] at ht
  have hswap : (∑' p : V × V, L p.swap) = ∑' p, L p := by
    simpa only [Equiv.prodComm_apply] using (Equiv.prodComm V V).tsum_eq L
  rw [hswap] at ht
  have hsum : (∑' p, L p) = (∑ x ∈ S, ∑' y, C x y * (a x - a y)^2) / R^2 := by
    rw [hL.tsum_prod, tsum_eq_sum (s := S)]
    · simp only [L]
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [ite_eq_left hx, tsum_div_const]
    · intro x hx
      simp [L, hx]
  rw [hsum] at ht
  dsimp [energy]
  linarith

private theorem cutoff_lipschitz {R : ℝ} (hR : 0 < R) (x y : ℝ) :
    |(Set.projIcc (0 : ℝ) 1 (by norm_num) (2 - |x| / R) : ℝ) - (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 - |y| / R) : ℝ)| ≤ |x - y| / R := by
  have h := (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) (by norm_num)).dist_le_mul
    (2 - |x| / R) (2 - |y| / R)
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] at h
  change |(Set.projIcc (0 : ℝ) 1 (by norm_num) (2 - |x| / R) : ℝ) - (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 - |y| / R) : ℝ)| ≤ _ at h
  apply h.trans
  rw [show 2 - |x| / R - (2 - |y| / R) = (|y| - |x|) / R by ring,
    abs_div, abs_of_pos hR, abs_sub_comm |y| |x|]
  exact div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y) hR.le

private theorem cutoff_one {R x : ℝ} (hR : 0 < R) (hx : |x| ≤ R) :
    (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 - |x| / R) : ℝ) = 1 := by
  have hq : |x| / R ≤ 1 := (div_le_one hR).mpr hx
  exact congrArg Subtype.val (Set.projIcc_of_right_le (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 1 ≤ 2 - |x| / R))

private theorem cutoff_zero {R x : ℝ} (hR : 0 < R) (hx : 2 * R ≤ |x|) :
    (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 - |x| / R) : ℝ) = 0 := by
  have hq : 2 ≤ |x| / R := (le_div_iff₀ hR).mpr hx
  exact congrArg Subtype.val (Set.projIcc_of_le_left (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 2 - |x| / R ≤ 0))

private theorem capacity_zero_of_second_moment_mass_bound {V : Type*}
    (C : V → V → ℝ) (hsymm : ∀ x y, C x y = C y x)
    (hnonneg : ∀ x y, 0 ≤ C x y) (hrow : ∀ x, Summable (C x))
    (a g : V → ℝ) (B A R0 : ℝ) (hB : 0 ≤ B)
    (hfinite : ∀ R : ℝ, 0 < R → {x | |a x| ≤ 2 * R}.Finite)
    (hmoment : ∀ x, Summable (fun y => C x y * (a x - a y)^2))
    (hbound : ∀ x, (∑' y, C x y * (a x - a y)^2) ≤ B * g x)
    (hmass : ∀ R : ℝ, R0 ≤ R → ∀ S : Finset V,
      (∀ x ∈ S, |a x| ≤ 2 * R) → (∑ x ∈ S, g x) ≤ A * R)
    (x0 : V) :
    ∀ ε : ℝ, 0 < ε → ∃ (S : Finset V) (f : V → ℝ),
      (∀ x, x ∉ S → f x = 0) ∧ f x0 = 1 ∧ energy C f < ε := by
  classical
  intro ε hε
  obtain ⟨R, hRlarge⟩ := exists_gt (max (max R0 |a x0|) (B * A / ε))
  have hR0 : R0 ≤ R := (le_max_left R0 |a x0|).trans ((le_max_left _ _).trans hRlarge.le)
  have hx0 : |a x0| ≤ R := (le_max_right R0 |a x0|).trans ((le_max_left _ _).trans hRlarge.le)
  have hR : 0 < R := (abs_nonneg (a x0)).trans_lt
    ((le_max_right R0 |a x0|).trans_lt ((le_max_left _ _).trans_lt hRlarge))
  have hRε : B * A / ε < R := (le_max_right _ _).trans_lt hRlarge
  let S := (hfinite R hR).toFinset
  let f : V → ℝ := fun x => (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 - |a x| / R) : ℝ)
  have hsupport : ∀ x, x ∉ S → f x = 0 := by
    intro x hx
    have hxout : ¬ |a x| ≤ 2 * R := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hx
    exact cutoff_zero hR (le_of_lt (lt_of_not_ge hxout))
  have hf0 : f x0 = 1 := cutoff_one hR hx0
  refine ⟨S, f, hsupport, hf0, ?_⟩
  have hLip (x y : V) : (f x - f y)^2 ≤ (a x - a y)^2 / R^2 := by
    have h := cutoff_lipschitz hR (a x) (a y)
    have hsq := (sq_le_sq₀ (abs_nonneg _) (div_nonneg (abs_nonneg _) hR.le)).mpr h
    simpa only [sq_abs, div_pow] using hsq
  have hE := energy_bound_by_supported_moments C hsymm hnonneg hrow a f S hsupport R hLip hmoment
  have hM : (∑ x ∈ S, ∑' y, C x y * (a x - a y)^2) ≤ B * A * R := by
    calc
      _ ≤ ∑ x ∈ S, B * g x := Finset.sum_le_sum (fun x _ => hbound x)
      _ = B * ∑ x ∈ S, g x := (Finset.mul_sum S _ _).symm
      _ ≤ B * (A * R) := mul_le_mul_of_nonneg_left (hmass R hR0 S (by
        intro x hx
        simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hx)) hB
      _ = B * A * R := by exact Eq.symm (mul_assoc B A R)
  have hEs : energy C f ≤ B * A / R := by
    calc
      energy C f ≤ (∑ x ∈ S, ∑' y, C x y * (a x - a y)^2) / R^2 := hE
      _ ≤ B * A * R / R^2 := div_le_div_of_nonneg_right hM (sq_nonneg _)
      _ = B * A / R := by field_simp
  apply hEs.trans_lt
  apply (div_lt_iff₀ hR).mpr
  have h := (div_lt_iff₀ hε).mp hRε
  nlinarith


private theorem reciprocal_constant_of_power_bound {s : ℝ} (hs : 2 < s)
    (a : ℤ → ℝ) (ha : StrictMono a)
    (hratio : ∀ j : ℤ, a (j + 1) - a j ≤ 2 * (a j - a (j - 1)))
    (hreverse : ∀ j : ℤ, a j - a (j - 1) ≤ 2 * (a (j + 1) - a j))
    (hfinite : ∀ R : ℝ, 0 < R → {j : ℤ | |a j| ≤ 2 * R}.Finite)
    (C : ℤ → ℤ → ℝ) (hsymm : ∀ x y, C x y = C y x)
    (hnonneg : ∀ x y, 0 ≤ C x y) (hpositive : ∀ x y, x ≠ y → 0 < C x y)
    (hrow : ∀ x, Summable (C x))
    (hweighted : ∀ x, Summable (fun y => C x y * (a (y + 1) - a y)⁻¹))
    (hharm : ∀ x, (∑' y, C x y * (a (y + 1) - a y)⁻¹) =
      (∑' y, C x y) * (a (x + 1) - a x)⁻¹)
    (K : ℝ) (hK : 0 ≤ K)
    (hC : ∀ x y, x ≠ y → C x y ≤ K * (a (x + 1) - a x) * (a (y + 1) - a y) * |a y - a x| ^ (-s - 1)) :
    ∀ x y, (a (x + 1) - a x)⁻¹ = (a (y + 1) - a y)⁻¹ := by
  classical
  let g : ℤ → ℝ := fun j => a (j + 1) - a j
  have hg (j : ℤ) : 0 < g j := sub_pos.mpr (ha (by omega))
  apply harmonic_constant_of_sublevel_capacity_zero C hsymm hnonneg hpositive hrow
    (fun j => (g j)⁻¹) (fun j => inv_pos.mpr (hg j)) hweighted hharm
  intro M hM _ x0
  let A : Set ℤ := {j | (g j)⁻¹ ≤ M}
  let D : A → A → ℝ := fun x y => C x.val y.val
  let b : A → ℝ := fun x => a x.val
  let G : A → ℝ := fun x => g x.val
  let δ : ℝ := 1 / (2 * M)
  let Q : ℝ := (1 + (2:ℝ)) * ((1 + (2:ℝ)) ^ (s - 1) * δ ^ (2 - s) / (s - 2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hfull (x : A) : Summable (fun j : ℤ => g j * |a j - a x.val| ^ (1 - s)) ∧
      (∑' j : ℤ, g j * |a j - a x.val| ^ (1 - s)) ≤ Q := by
    have hx : (g x.val)⁻¹ ≤ M := x.property
    have hxmul : 1 ≤ M * g x.val := by
      exact (inv_le_iff_one_le_mul₀ (hg x.val)).mp hx
    have hgap : δ ≤ g x.val := by
      dsimp [δ]
      apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
      nlinarith
    have hprev : δ ≤ a x.val - a (x.val - 1) := by
      have H := hratio x.val
      change g x.val ≤ 2 * (a x.val - a (x.val - 1)) at H
      dsimp [δ]
      apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
      nlinarith
    exact full_weighted_distance ha 2 s δ (by norm_num) hs hδ hratio hreverse x.val hgap hprev
  have hWnonneg (x j : ℤ) : 0 ≤ g j * |a j - a x| ^ (1 - s) :=
    mul_nonneg (hg j).le (Real.rpow_nonneg (abs_nonneg _) _)
  have hW (x : A) : Summable (fun y : A => G y * |b y - b x| ^ (1 - s)) := (hfull x).1.subtype A
  have hWbound (x : A) : (∑' y : A, G y * |b y - b x| ^ (1 - s)) ≤ Q := by
    exact (Summable.tsum_subtype_le _ A (hWnonneg x.val) (hfull x).1).trans (hfull x).2
  have hmoment (x : A) := inverse_power_second_moment D (fun x y => hnonneg x.val y.val)
    b G K s hK (fun x => (hg x.val).le)
    (fun x y hxy => hC x.val y.val (fun h => hxy (Subtype.ext h)))
    (fun x y h => Subtype.ext (ha.injective h)) x (hW x)
  have hmoment_bound (x : A) : (∑' y : A, D x y * (b x - b y)^2) ≤ (K * Q) * G x := by
    calc
      _ ≤ K * G x * (∑' y : A, G y * |b y - b x| ^ (1 - s)) := (hmoment x).2
      _ ≤ K * G x * Q := mul_le_mul_of_nonneg_left (hWbound x) (mul_nonneg hK (hg x.val).le)
      _ = _ := by exact mul_right_comm K (G x) Q
  let R0 : ℝ := max 1 (max |a 0| |a 1|)
  have hmass (R : ℝ) (hR0 : R0 ≤ R) (S : Finset A) (hS : ∀ x ∈ S, |b x| ≤ 2 * R) :
      (∑ x ∈ S, G x) ≤ 12 * R := by
    have hR : 0 ≤ R := by dsimp [R0] at hR0; linarith [le_max_left (1:ℝ) (max |a 0| |a 1|)]
    have ha0 : |a 0| ≤ 2 * R := by
      have H := (le_max_left |a 0| |a 1|).trans ((le_max_right (1:ℝ) _).trans hR0)
      linarith
    have ha1 : |a 1| ≤ 2 * R := by
      have H := (le_max_right |a 0| |a 1|).trans ((le_max_right (1:ℝ) _).trans hR0)
      linarith
    let T : Finset ℤ := S.image Subtype.val
    have hT : ∀ j ∈ T, |a j| ≤ 2 * R := by
      intro j hj
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      exact hS x hx
    have H := window_gap_mass ha (by norm_num : (1:ℝ) ≤ 2) hR hratio 0 1 (by norm_num) ha0 ha1 T hT
    have heq : (∑ j ∈ T, (a (j + 1) - a j)) = ∑ x ∈ S, G x := by
      dsimp [T, G, g]
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact Subtype.ext hxy
    rw [heq] at H
    norm_num at H
    exact H
  exact capacity_zero_of_second_moment_mass_bound D (fun x y => hsymm x.val y.val)
    (fun x y => hnonneg x.val y.val) (fun x => (hrow x.val).subtype A)
    b G (K * Q) 12 R0 (mul_nonneg hK hQ)
    (fun R hR => (hfinite R hR).preimage (f := fun x : A => x.val) Subtype.val_injective.injOn)
    (fun x => (hmoment x).1) hmoment_bound hmass x0

private theorem equilibrium_is_progression {s : ℝ} (hs : 2 < s) {X : Set ℝ}
    (hX : IsSEquilibrium s X) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, X = arithmeticProgression α β := by
  classical
  obtain ⟨a, ha, hrange⟩ := equilibrium_enumeration hX
  have hf := equilibrium_indexed_force hX ha hrange
  have ht := equilibrium_indexed_total hX ha hrange
  have hratio := equilibrium_gap_ratio hs ha hf
  have hreverse := equilibrium_gap_reverse hs ha hf
  have hg (n : ℤ) : 0 < fwdDiff 1 a n := sub_pos.mpr (ha (by omega))
  have hrev : ∀ n, fwdDiff 1 a n ≤ 2 * fwdDiff 1 a (n + 1) := by
    intro n
    have H := hreverse (n + 1)
    simpa only [fwdDiff, add_sub_cancel_right] using H
  have hc := conductance_rows (by linarith : 0 < s) ha hrev ht
  have hw := gaps_harmonic ha hf hc
  let C : ℤ → ℤ → ℝ := fun n j => conductance s a n j * fwdDiff 1 a n * fwdDiff 1 a j
  have hC := reciprocal_transform (conductance s a) (fwdDiff 1 a) hg hc hw.1 hw.2
  have hcpos (n j : ℤ) : 0 ≤ conductance s a n j := by
    by_cases hnj : n = j
    · simp [conductance, hnj]
    · exact (conductance_positive (by linarith) ha n j hnj).le
  have hsymm (n j : ℤ) : C n j = C j n := by
    dsimp [C]
    rw [conductance_symmetric s a n j]
    ring
  have hnonneg (n j : ℤ) : 0 ≤ C n j :=
    mul_nonneg (mul_nonneg (hcpos n j) (hg n).le) (hg j).le
  have hpositive (n j : ℤ) (hnj : n ≠ j) : 0 < C n j :=
    mul_pos (mul_pos (conductance_positive (by linarith) ha n j hnj) (hg n)) (hg j)
  have hfinite (R : ℝ) (hR : 0 < R) : {j : ℤ | |a j| ≤ 2 * R}.Finite := by
    apply ((hX.2.2.1 (-2 * R) (2 * R)).preimage ha.injective.injOn).subset
    intro j hj
    exact ⟨hrange ▸ ⟨j, rfl⟩, by simpa only [neg_mul, Set.mem_Icc] using abs_le.mp hj⟩
  let K : ℝ := s / (3:ℝ) ^ (-s - 1)
  have hK : 0 ≤ K := div_nonneg (by linarith) (Real.rpow_pos_of_pos (by norm_num) _).le
  have hbound (n j : ℤ) (hnj : n ≠ j) :
      C n j ≤ K * (a (n + 1) - a n) * (a (j + 1) - a j) * |a j - a n| ^ (-s - 1) := by
    have H := mul_le_mul_of_nonneg_right (conductance_distance_bound (by linarith : 0 < s) ha hrev n j hnj)
      (mul_nonneg (hg n).le (hg j).le)
    dsimp [C, K, fwdDiff] at *
    nlinarith [H]
  have hconstant := reciprocal_constant_of_power_bound hs a ha hratio hreverse hfinite C hsymm
    hnonneg hpositive hC.1 hC.2.1 hC.2.2 K hK hbound
  have hgap : ∀ n : ℤ, a (n + 1) - a n = fwdDiff 1 a 0 := by
    intro n
    exact inv_injective (hconstant n 0)
  have haff := constant_gap_affine hgap
  refine ⟨fwdDiff 1 a 0, hg 0, a 0, ?_⟩
  rw [← hrange]
  unfold arithmeticProgression
  congr 1
  funext n
  exact haff n

theorem result : claim := by
  intro s hs
  refine ⟨equilibrium_exists (by linarith), ?_⟩
  intro X
  constructor
  · exact equilibrium_is_progression hs
  · rintro ⟨α, hα, β, rfl⟩
    exact progression_equilibrium (by linarith) hα

end D5.S3.StatisticalMechanics.InversePowerLineEquilibria
