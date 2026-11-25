/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity, mathlib/module/Mathlib.Data.Fintype.Perm]
   utility: none
   digest: Universal real Huang boundary kernels force a cover by higher-contact axis orders. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactOrderCoverage
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary
import Mathlib.Data.Fin.Embedding

/-!
# Higher-contact coordinate-order obstruction

For each ordering of the active coordinates, use powers of a real base greater
than the number of active coordinates. At a maximal absolute kernel entry,
every adjacent empty row must admit a strictly higher-ranked contact whose
signed contribution opposes the maximal entry's contribution.

This yields a cover of the rank permutations by axis-graph local orders, for
arbitrary contact multiplicities in the actual Huang cube.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.GeneralContactOrderCoverage

open scoped BigOperators Matrix
open BalancedCriticalSpectrum (Q flip flip_flip)
open BalancedCubeGirth (flip_comm)
open Q9IsotropicHuang (flipSign parity flip_off_parity)

variable {m n : ℕ}

/-- A supported nonzero kernel on the empty rows for every real weighting of
the active axes. An embedding permits application to coordinate fibres. -/
def HasUniversalEmptyKernel (a : Fin n ↪ Fin m) (K : Finset (Q m))
    (occupied : Q m → Bool) : Prop :=
  ∀ w : Fin n → ℝ, ∃ f : Q m → ℝ, f ≠ 0 ∧
    (∀ q, q ∉ K → f q = 0) ∧
    ∀ r, occupied r = false →
      (∑ i, w i * (flipSign (a i) r : ℝ) * f (flip r (a i))) = 0

private theorem flipSign_abs {d : ℕ} (i : Fin d) (x : Q d) :
    |(flipSign i x : ℝ)| = 1 := by
  have hs : flipSign i x = 1 ∨ flipSign i x = -1 := by
    induction d with
    | zero => exact Fin.elim0 i
    | succ d ih =>
        refine Fin.cases ?_ (fun j => ?_) i
        · exact Or.inl rfl
        · rcases ih j (Sensitivity.π x) with h | h <;>
            cases hx : x 0 <;> simp [flipSign, hx, h]
  rcases hs with h | h <;> simp [h]

/-- Geometric weights turn cancellation at a largest-magnitude entry into
an opposing contribution of strictly higher rank, even in a row with many
nonzero entries. -/
private theorem exists_higher_opposing (c : Equiv.Perm (Fin n)) (u : Fin n → ℝ)
    (i : Fin n) (hi : u i ≠ 0) (hmax : ∀ j, |u j| ≤ |u i|)
    (hzero : (∑ j, ((n : ℝ) + 1) ^ (c j).val * u j) = 0) :
    ∃ j, c i < c j ∧ u i * u j < 0 := by
  classical
  let B : ℝ := (n : ℝ) + 1
  let w (j : Fin n) : ℝ := B ^ (c j).val
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hw (j : Fin n) : 0 < w j := pow_pos hBpos _
  let M : ℝ := w i * (u i * u i)
  have hM : 0 < M := mul_pos (hw i) (mul_self_pos.mpr hi)
  let T (j : Fin n) : ℝ := B * w j * (u i * u j)
  have hTi : T i = B * M := by dsimp [T, M]; ring
  have hsum : (∑ j, T j) = 0 := by
    calc
      _ = (B * u i) * ∑ j, w j * u j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [T]
        ring
      _ = 0 := by
        have hz : (∑ j, w j * u j) = 0 := hzero
        rw [hz, mul_zero]
  by_contra hn
  push Not at hn
  have hlower (j : Fin n) (hj : j ≠ i) : -M ≤ T j := by
    by_cases horder : c i < c j
    · have hnonneg : 0 ≤ u i * u j := hn j horder
      have ht : 0 ≤ T j :=
        mul_nonneg (mul_nonneg hBpos.le (hw j).le) hnonneg
      exact (neg_nonpos.mpr hM.le).trans ht
    · have hlt : (c j).val < (c i).val := by
        exact lt_of_le_of_ne (le_of_not_gt horder)
          (fun h => hj (c.injective (Fin.val_injective h)))
      have hpow : B * w j ≤ w i := by
        calc
          _ = B ^ ((c j).val + 1) := by
            dsimp [w]
            rw [pow_succ]
            exact mul_comm _ _
          _ ≤ _ := pow_le_pow_right₀ hB (by omega)
      have hu : |u i| * |u j| ≤ u i * u i := by
        rw [← abs_mul_abs_self (u i)]
        exact mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg _)
      have hbound : |T j| ≤ M := by
        calc
          _ = (B * w j) * (|u i| * |u j|) := by
            simp only [T, abs_mul, abs_of_pos hBpos, abs_of_pos (hw j)]
          _ ≤ _ := mul_le_mul hpow hu
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hw i).le
      exact (neg_le_neg hbound).trans (neg_abs_le _)
  let E := (Finset.univ : Finset (Fin n)).erase i
  have hcard : E.card ≤ n := by
    simpa only [E, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.erase_subset i (Finset.univ : Finset (Fin n)))
  have hcardReal : (E.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
  have hrest : -(n : ℝ) * M ≤ ∑ j ∈ E, T j := by
    calc
      _ = (n : ℝ) * (-M) := by ring
      _ ≤ (E.card : ℝ) * (-M) :=
        mul_le_mul_of_nonpos_right hcardReal (neg_nonpos.mpr hM.le)
      _ = ∑ _j ∈ E, -M := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => hlower j (Finset.mem_erase.mp hj).1
  have hsplit : (∑ j ∈ E, T j) + T i = 0 :=
    (Finset.sum_erase_add Finset.univ T (Finset.mem_univ i)).trans hsum
  rw [hTi] at hsplit
  have hpos : 0 < (∑ j ∈ E, T j) + B * M := by
    calc
      0 < M := hM
      _ = -(n : ℝ) * M + B * M := by dsimp [B]; ring
      _ ≤ _ := by linarith only [hrest]
  exact (ne_of_gt hpos) hsplit

/-- For any order there is a single maximal nonzero kernel column such that
every empty direction has an opposing higher-ranked contact in the same
kernel. The displayed product uses the signed real Huang row coefficients. -/
theorem exists_signed_higher_contact (a : Fin n ↪ Fin m) (K : Finset (Q m))
    (occupied : Q m → Bool) (hker : HasUniversalEmptyKernel a K occupied)
    (c : Equiv.Perm (Fin n)) :
    ∃ f : Q m → ℝ, f ≠ 0 ∧ (∀ x, x ∉ K → f x = 0) ∧
      (∀ r, occupied r = false →
        (∑ i, ((n : ℝ) + 1) ^ (c i).val *
          (flipSign (a i) r : ℝ) * f (flip r (a i))) = 0) ∧
      ∃ q ∈ K, f q ≠ 0 ∧ (∀ x, |f x| ≤ |f q|) ∧
        ∀ i, occupied (flip q (a i)) = false →
          ∃ j, c i < c j ∧ flip (flip q (a i)) (a j) ∈ K ∧
            ((flipSign (a i) (flip q (a i)) : ℝ) * f q) *
              ((flipSign (a j) (flip q (a i)) : ℝ) *
                f (flip (flip q (a i)) (a j))) < 0 := by
  classical
  obtain ⟨f, hf, hsupp, hrow⟩ := hker (fun i => ((n : ℝ) + 1) ^ (c i).val)
  have hex : ∃ x, f x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hf (funext hn)
  obtain ⟨x, hx⟩ := hex
  obtain ⟨q, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Q m))
    (fun x => |f x|) ⟨x, Finset.mem_univ x⟩
  have hmax' (y : Q m) : |f y| ≤ |f q| := hmax y (Finset.mem_univ y)
  have hq : f q ≠ 0 := by
    intro h
    have hh := hmax' x
    rw [h, abs_zero] at hh
    exact (not_le_of_gt (abs_pos.mpr hx)) hh
  have hqK : q ∈ K := by
    by_contra h
    exact hq (hsupp q h)
  refine ⟨f, hf, hsupp, hrow, q, hqK, hq, hmax', ?_⟩
  intro i hi
  let r := flip q (a i)
  let u (j : Fin n) : ℝ := (flipSign (a j) r : ℝ) * f (flip r (a j))
  have hu (j : Fin n) : |u j| = |f (flip r (a j))| := by
    simp only [u, abs_mul, flipSign_abs, one_mul]
  have hui : |u i| = |f q| := by
    simp only [hu, r, BalancedCriticalSpectrum.flip_flip]
  have hune : u i ≠ 0 := by
    intro h
    rw [h, abs_zero] at hui
    exact (abs_ne_zero.mpr hq) hui.symm
  have humax (j : Fin n) : |u j| ≤ |u i| := by
    rw [hu, hui]
    exact hmax' _
  have hsum : (∑ j, ((n : ℝ) + 1) ^ (c j).val * u j) = 0 := by
    simpa only [u, ← mul_assoc] using hrow r hi
  obtain ⟨j, hj, hneg⟩ := exists_higher_opposing c u i hune humax hsum
  have hp : flip r (a j) ∈ K := by
    by_contra hn
    have hh : u j = 0 := by simp [u, hsupp _ hn]
    rw [hh, mul_zero] at hneg
    exact (lt_irrefl 0) hneg
  refine ⟨j, hj, hp, ?_⟩
  simpa only [u, r, BalancedCriticalSpectrum.flip_flip] using hneg

/-- Local coordinate orders of a graph with a distinguished target set:
every axis outside the target set has a higher-ranked neighbor. -/
def localOrders (edge : Fin n → Fin n → Prop) (target : Fin n → Prop) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter fun c =>
    ∀ i, ¬ target i → ∃ j, edge i j ∧ c i < c j

@[simp] theorem mem_localOrders (edge : Fin n → Fin n → Prop) (target : Fin n → Prop)
    (c : Equiv.Perm (Fin n)) :
    c ∈ localOrders edge target ↔
      ∀ i, ¬ target i → ∃ j, edge i j ∧ c i < c j := by
  classical
  simp [localOrders]

/-- Relabeling all axes by a permutation preserves the number of local orders.
The bijection is right multiplication on the group of rank permutations. -/
theorem card_localOrders_relabel (edge : Fin n → Fin n → Prop) (target : Fin n → Prop)
    (g : Equiv.Perm (Fin n)) :
    (localOrders edge target).card =
      (localOrders (fun i j => edge (g i) (g j)) (fun i => target (g i))).card := by
  classical
  refine Finset.card_equiv (Equiv.mulRight g) ?_
  intro c
  simp only [mem_localOrders]
  change (∀ i, ¬ target i → ∃ j, edge i j ∧ c i < c j) ↔
    ∀ i, ¬ target (g i) → ∃ j, edge (g i) (g j) ∧ c (g i) < c (g j)
  constructor
  · intro h i hi
    obtain ⟨j, he, hj⟩ := h (g i) hi
    obtain ⟨k, rfl⟩ := g.surjective j
    exact ⟨k, he, hj⟩
  · intro h i hi
    obtain ⟨k, rfl⟩ := g.surjective i
    obtain ⟨j, he, hj⟩ := h k hi
    exact ⟨g j, he, hj⟩

/-- An edge of the axis graph at a column means that the opposite corner of
the corresponding coordinate square is also selected. -/
def axisEdge (a : Fin n ↪ Fin m) (K : Finset (Q m)) (q : Q m)
    (i j : Fin n) : Prop :=
  i ≠ j ∧ flip (flip q (a i)) (a j) ∈ K

theorem axisEdge_symm (a : Fin n ↪ Fin m) (K : Finset (Q m)) (q : Q m) :
    Symmetric (axisEdge a K q) := by
  intro i j h
  refine ⟨h.1.symm, ?_⟩
  rw [flip_comm]
  exact h.2

/-- The target axes are exactly those incident to occupied rows. -/
def cubeOrders (a : Fin n ↪ Fin m) (K : Finset (Q m))
    (occupied : Q m → Bool) (q : Q m) : Finset (Equiv.Perm (Fin n)) :=
  localOrders (axisEdge a K q) (fun i => occupied (flip q (a i)) = true)

/-- The local axis-graph orders cover every coordinate permutation. -/
theorem exists_mem_cubeOrders (a : Fin n ↪ Fin m) (K : Finset (Q m))
    (occupied : Q m → Bool) (hker : HasUniversalEmptyKernel a K occupied)
    (c : Equiv.Perm (Fin n)) :
    ∃ q ∈ K, c ∈ cubeOrders a K occupied q := by
  obtain ⟨f, hf, hs, hr, q, hq, hne, hmax, hgood⟩ :=
    exists_signed_higher_contact a K occupied hker c
  refine ⟨q, hq, (mem_localOrders _ _ _).mpr ?_⟩
  intro i hi
  have hempty : occupied (flip q (a i)) = false := Bool.eq_false_of_not_eq_true hi
  obtain ⟨j, hj, hp, _⟩ := hgood i hempty
  exact ⟨j, ⟨fun h => (ne_of_lt hj) (congrArg c h), hp⟩, hj⟩

/-- The general higher-contact permutation-cover inequality. -/
theorem factorial_le_sum_card_cubeOrders (a : Fin n ↪ Fin m) (K : Finset (Q m))
    (occupied : Q m → Bool) (hker : HasUniversalEmptyKernel a K occupied) :
    n.factorial ≤ ∑ q ∈ K, (cubeOrders a K occupied q).card := by
  classical
  have hcover : (Finset.univ : Finset (Equiv.Perm (Fin n))) =
      K.biUnion (cubeOrders a K occupied) := by
    apply Finset.Subset.antisymm
    · intro c _
      exact Finset.mem_biUnion.mpr (exists_mem_cubeOrders a K occupied hker c)
    · exact Finset.subset_univ _
  calc
    _ = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    _ = (K.biUnion (cubeOrders a K occupied)).card := congrArg Finset.card hcover
    _ ≤ _ := Finset.card_biUnion_le

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.GeneralContactOrderCoverage

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.GeneralContactOrderCoverage

open scoped BigOperators Matrix
open BalancedCriticalSpectrum (Q flip)
open Q9IsotropicHuang (flipSign parity flip_off_parity weightedLinear_apply weightedAction)
open Q9WeightedBoundaryGram (signed signed_mulVec)
open CoordinateHalves.Q9DominantAxisBoundary (PairedRows EmptyExterior emptyFibreBoundary
  exists_two_components_with_fixed_projectedParity_emptyFibre_kernels)
open TwoBalancedComponents (componentFinset)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)

/-- Retained representatives of the actual paired fibres at transverse parity
`p`. Full parity `b` chooses exactly one lift from each such fibre. -/
def pairedClass (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (p : Bool) : Finset (Q 9) :=
  Finset.univ.filter fun q =>
    q ∈ C ∧ BalancedCriticalSpectrum.flip q i ∈ C ∧ parity q = b ∧
      (∑ j : Fin 8, q (i.succAbove j)) = p

/-- Fibre occupancy is independent of which lift represents the fibre. -/
def fibreOccupied (C : Finset (Q 9)) (i : Fin 9) (r : Q 9) : Bool :=
  decide (r ∈ C ∨ flip r i ∈ C)

/-- Extend the actual restricted matrix kernel by zero to the ambient cube.
The eight active coordinate weights are precisely the transverse weights. -/
theorem universalEmptyKernel_of_fixed_projectedParity (C : Finset (Q 9))
    (b : Bool) (i : Fin 9) (p : Bool)
    (hk : ∀ v : Fin 9 → ℝ, ∃ g : PairedRows C b i → ℝ,
      g ≠ 0 ∧ emptyFibreBoundary C b i v *ᵥ g = 0 ∧
      ∀ x, (∑ j : Fin 8, x.1.1.1 (i.succAbove j)) ≠ p → g x = 0) :
    HasUniversalEmptyKernel i.succAboveEmb (pairedClass C b i p) (fibreOccupied C i) := by
  classical
  intro w
  let v : Fin 9 → ℝ := Function.extend i.succAbove w (fun _ => 0)
  have hv (k : Fin 8) : v (i.succAbove k) = w k :=
    Fin.succAbove_right_injective.extend_apply _ _ _
  obtain ⟨g, hg, hmat, hproj⟩ := hk v
  let col (x : PairedRows C b i) : Q 9 := x.1.1.1
  have hcolinj : Function.Injective col := by
    intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  let f := Function.extend col g (fun _ : Q 9 => (0 : ℝ))
  have hfcol (x : PairedRows C b i) : f (col x) = g x :=
    hcolinj.extend_apply _ _ _
  have hfzero (q : Q 9) (hq : ¬ ∃ x, col x = q) : f q = 0 :=
    Function.extend_apply' _ _ _ hq
  have hsupp (q : Q 9) (hq : q ∉ pairedClass C b i p) : f q = 0 := by
    by_cases hex : ∃ x, col x = q
    · obtain ⟨x, rfl⟩ := hex
      rw [hfcol]
      apply hproj
      intro hp
      apply hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        x.1.1.property, x.property, (Finset.mem_filter.mp x.1.property).2, hp⟩
    · exact hfzero q hex
  refine ⟨f, ?_, hsupp, ?_⟩
  · intro hz
    apply hg
    funext x
    exact (hfcol x).symm.trans (congrFun hz (col x))
  · intro r hr
    have hempty : r ∉ C ∧ flip r i ∉ C := by
      simpa [fibreOccupied, not_or] using hr
    by_cases hpar : parity r = b
    · apply Finset.sum_eq_zero
      intro j _
      have hflip : parity (flip r (i.succAbove j)) ≠ b :=
        flip_off_parity _ (by rw [hpar]; cases b <;> decide)
      have hn : flip r (i.succAbove j) ∉ pairedClass C b i p :=
        fun hm => hflip (Finset.mem_filter.mp hm).2.2.2.1
      change w j * (flipSign (i.succAbove j) r : ℝ) *
          f (flip r (i.succAbove j)) = 0
      rw [hsupp _ hn, mul_zero]
    · let y : EmptyExterior C b i := ⟨⟨⟨r, hpar⟩, hempty.1⟩, hempty.2⟩
      let v' (j : Fin 9) : ℝ := if j = i then 0 else v j
      have hentry (x : PairedRows C b i) :
          emptyFibreBoundary C b i v y x = signed v' r (col x) := rfl
      have hsum : (signed v' *ᵥ f) r = (emptyFibreBoundary C b i v *ᵥ g) y := by
        simp only [Matrix.mulVec, dotProduct, hentry]
        symm
        refine Fintype.sum_of_injective col hcolinj _ _ ?_ ?_
        · intro q hq
          rw [hfzero q hq, mul_zero]
        · intro x
          rw [hfcol]
      have hzero : (signed v' *ᵥ f) r = 0 :=
        hsum.trans (congrFun hmat y)
      rw [signed_mulVec, weightedLinear_apply] at hzero
      change (∑ j : Fin 9, v' j * (flipSign j r : ℝ) * f (flip r j)) = 0 at hzero
      rw [Fin.sum_univ_succAbove _ i] at hzero
      have hi : v' i = 0 := by simp [v']
      rw [hi, zero_mul, zero_mul, zero_add] at hzero
      change (∑ j : Fin 8, w j * (flipSign (i.succAbove j) r : ℝ) *
          f (flip r (i.succAbove j))) = 0
      simpa only [v', ite_eq_right (Fin.succAbove_ne i _), hv] using hzero

open Classical in
/-- Each of two distinct actual components of a hypothetical 258-vertex
subcubic Q9 support passes the higher-contact order-cover bound on a fixed
projected parity along every dominant axis. -/
theorem exists_two_components_with_higherContact_orderCoverage
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (b : Bool) :
    ∃ C D : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      C ≠ D ∧ ∀ i : Fin 9, ∃ pC pD : Bool,
        (40320 ≤ ∑ q ∈ pairedClass (componentFinset U C) b i pC,
          (cubeOrders i.succAboveEmb (pairedClass (componentFinset U C) b i pC)
            (fibreOccupied (componentFinset U C) i) q).card) ∧
        (40320 ≤ ∑ q ∈ pairedClass (componentFinset U D) b i pD,
          (cubeOrders i.succAboveEmb (pairedClass (componentFinset U D) b i pD)
            (fibreOccupied (componentFinset U D) i) q).card) := by
  classical
  obtain ⟨C, D, hCD, hk⟩ :=
    exists_two_components_with_fixed_projectedParity_emptyFibre_kernels U hU hdeg b
  refine ⟨C, D, hCD, fun i => ?_⟩
  obtain ⟨pC, pD, hp⟩ := hk i
  have hC := universalEmptyKernel_of_fixed_projectedParity (componentFinset U C) b i pC
    (fun v => by simpa only [Finset.mem_univ, ite_true] using (hp Finset.univ v).1)
  have hD := universalEmptyKernel_of_fixed_projectedParity (componentFinset U D) b i pD
    (fun v => by simpa only [Finset.mem_univ, ite_true] using (hp Finset.univ v).2)
  refine ⟨pC, pD, ?_, ?_⟩
  · exact (show 40320 = (8 : ℕ).factorial by decide).le.trans
      (factorial_le_sum_card_cubeOrders _ _ _ hC)
  · exact (show 40320 = (8 : ℕ).factorial by decide).le.trans
      (factorial_le_sum_card_cubeOrders _ _ _ hD)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.GeneralContactOrderCoverage
