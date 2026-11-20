/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarPartnerBound
   generality: I
   mirror-B: none(waiver:standalone-research-source)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A size bound for separated balanced cubic partners of the nine-cube star. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! The star and the integer multipliers are from the four-axis proof
(GPT Pro task d6c45d83-675a-442b-bee6-dea2bae0c87d), with the certificate
reproduced in `q9_star_partner_certificate.py`. The sums below run over
actual cube vertices. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerBound

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj IsBalanced direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions exterior_even)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open BalancedCubeGirth (no_selected_square)

local notation "flip" => BalancedCriticalSpectrum.flip

private def pairCount (x : Q 9) (a b : Bool) : Nat :=
  (if x 0 == a && x 1 == b then 1 else 0) +
  (if x 2 == a && x 3 == b then 1 else 0) +
  (if x 4 == a && x 5 == b then 1 else 0)

private def outerCount (x : Q 9) : Nat :=
  (if x 6 then 1 else 0) + (if x 7 then 1 else 0) + (if x 8 then 1 else 0)

private def kind (x : Q 9) : Nat × Nat × Nat :=
  (pairCount x false true, pairCount x true false, outerCount x)

private def inStar (x : Q 9) : Bool :=
  match kind x with
  | (0, 0, 1) | (0, 1, 1) | (0, 1, 0) => true
  | _ => false

/-- The star uses the three consecutive base pairs and the last three outer coordinates. -/
def Sstar : Finset (Q 9) := Finset.univ.filter fun x => inStar x = true

private def eligible (x : Q 9) : Bool :=
  !inStar x && (List.finRange 9).all fun i => !inStar (flip x i)

private def B (x : Q 9) : Bool :=
  let (r, g, k) := kind x
  if k ≤ 1 then decide (2 ≤ r)
  else if k = 2 then decide (1 ≤ r ∨ 2 ≤ g)
  else true

private def dirs (p : Q 9 → Bool) (x : Q 9) : Finset (Fin 9) :=
  Finset.univ.filter fun i => p (flip x i) = true

private def outerDirs : Finset (Fin 9) := {6, 7, 8}

/-- Base labels 21, 22, 25 and 37 in little-endian order. -/
private def forcedBase (x : Q 9) : Bool :=
  let (r, g, _) := kind x
  (r == 0 && g == 3) || (r == 1 && g == 2)

private def singletonDir (x : Q 9) : Fin 9 :=
  if x 6 then 6 else if x 7 then 7 else 8

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Count the selected vertices by kernel reduction over the 512 cube points.
theorem star_card : Sstar.card = 72 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the eligible direction set over all 512 cube points.
private theorem forced_dirs :
    ∀ x : Q 9, forcedBase x = true → outerCount x ≤ 1 → dirs eligible x = outerDirs := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check which of the outer flips link roots and singletons over the cube.
private theorem forced_flips :
    ∀ x : Q 9, forcedBase x = true →
      (outerCount x = 0 →
        forcedBase (flip x 6) = true ∧ outerCount (flip x 6) = 1) ∧
      (outerCount x = 1 →
        singletonDir x ∈ outerDirs ∧
          forcedBase (flip x (singletonDir x)) = true ∧
          outerCount (flip x (singletonDir x)) = 0) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the eligible-region partition and its low-degree vertices over the cube.
private theorem eligible_cases :
    ∀ x : Q 9, eligible x = true →
      B x = true ∨ (forcedBase x = true ∧ outerCount x ≤ 1) ∨
        (kind x = (1, 0, 0) ∧ (dirs eligible x).card = 2) := by
  decide +kernel

private theorem eligible_of_separated {D : Finset (Q 9)}
    (hdisj : Disjoint Sstar D)
    (hcross : ∀ s ∈ Sstar, ∀ d ∈ D, ¬ (hypercube 9).Adj s d)
    {v : Q 9} (hv : v ∈ D) : eligible v = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, List.all_eq_true.mpr ?_⟩
  · cases h : inStar v with
    | false => rfl
    | true => exact (Finset.disjoint_left.mp hdisj (by simp [Sstar, h]) hv).elim
  · intro i _
    cases h : inStar (flip v i) with
    | false => rfl
    | true => exact (hcross _ (by simp [Sstar, h]) v hv (flip_adj v i).symm).elim

private theorem directions_subset {D : Finset (Q 9)} {p : Q 9 → Bool}
    (h : ∀ x ∈ D, p x = true) (v : Q 9) : directions D v ⊆ dirs p v := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h _ ((mem_directions D v i).mp hi)⟩

open Classical in
private theorem forced_exclusion {D : Finset (Q 9)}
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D)
    (hD : ∀ x ∈ D, eligible x = true)
    {v : Q 9} (hbase : forcedBase v = true) (hout : outerCount v ≤ 1) : v ∉ D := by
  have force {x : Q 9} (hx : x ∈ D) (hbase' : forcedBase x = true)
      (hout' : outerCount x ≤ 1) : directions D x = outerDirs := by
    apply Finset.eq_of_subset_of_card_le
    · simpa only [forced_dirs x hbase' hout'] using directions_subset hD x
    · rw [regular_directions D hr hx]
      decide
  have root {x : Q 9} (hbase' : forcedBase x = true)
      (hzero : outerCount x = 0) : x ∉ D := by
    intro hx
    have hxdir := force hx hbase' (hzero ▸ Nat.zero_le 1)
    have hx6 : flip x 6 ∈ D :=
      (mem_directions _ _ _).mp (hxdir ▸ (by decide : (6 : Fin 9) ∈ outerDirs))
    have hx7 : flip x 7 ∈ D :=
      (mem_directions _ _ _).mp (hxdir ▸ (by decide : (7 : Fin 9) ∈ outerDirs))
    obtain ⟨h6base, h6one⟩ := (forced_flips x hbase').1 hzero
    have h6dir := force hx6 h6base (le_of_eq h6one)
    exact no_selected_square hb (by decide : (6 : Fin 9) ≠ 7) hx hx6 hx7
      ((mem_directions _ _ _).mp (h6dir ▸ (by decide : (7 : Fin 9) ∈ outerDirs)))
  by_cases hzero : outerCount v = 0
  · exact root hbase hzero
  · intro hv
    have hone : outerCount v = 1 := by omega
    obtain ⟨hi, hibase, hizero⟩ := (forced_flips v hbase).2 hone
    exact root hibase hizero ((mem_directions _ _ _).mp (force hv hbase hout ▸ hi))

open Classical in
private theorem partner_subset_B {D : Finset (Q 9)}
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D)
    (hD : ∀ x ∈ D, eligible x = true) : ∀ x ∈ D, B x = true := by
  intro x hx
  rcases eligible_cases x (hD x hx) with hB | ⟨hbase, hout⟩ | ⟨_, htwo⟩
  · exact hB
  · exact (forced_exclusion hr hb hD hbase hout hx).elim
  · have hle := Finset.card_le_card (directions_subset hD x)
    rw [regular_directions D hr hx, htwo] at hle
    omega

/-! Each row gives the multipliers of the upper, lower, and indicator bounds. -/
private def multipliers : Nat × Nat × Nat → Nat × Nat × Nat
  | (0, 0, 3) => (2, 0, 0)
  | (0, 1, 2) => (5, 0, 0)
  | (0, 1, 3) => (1, 0, 0)
  | (0, 2, 3) => (2, 0, 0)
  | (0, 3, 2) => (2, 0, 0)
  | (1, 0, 2) => (0, 3, 1)
  | (1, 0, 3) => (4, 0, 0)
  | (1, 1, 0) => (9, 0, 0)
  | (1, 1, 1) => (22, 0, 0)
  | (1, 1, 2) => (5, 0, 0)
  | (1, 1, 3) => (1, 0, 0)
  | (1, 2, 2) => (4, 0, 1)
  | (2, 0, 0) => (0, 3, 1)
  | (2, 0, 1) => (0, 4, 1)
  | (2, 0, 2) => (10, 0, 0)
  | (2, 1, 3) => (1, 0, 0)
  | (3, 0, 0) => (1, 0, 0)
  | (3, 0, 1) => (2, 0, 0)
  | (3, 0, 3) => (0, 1, 0)
  | _ => (0, 0, 0)

private def orbitSize (q : Nat × Nat × Nat) : Nat :=
  let (r, g, k) := q
  let e := 3 - r - g
  (6 / (r.factorial * g.factorial * e.factorial)) * 2 ^ e * (if k = 0 ∨ k = 3 then 1 else 3)

private def scale (x : Q 9) (m : Nat) : Int :=
  (288 * m / orbitSize (kind x) : Nat)

private def upper (x : Q 9) : Int := scale x (multipliers (kind x)).1
private def lower (x : Q 9) : Int := scale x (multipliers (kind x)).2.1
private def box (x : Q 9) : Int := scale x (multipliers (kind x)).2.2

private def cap (x : Q 9) : Int := (2 * ((dirs B x).card / 2) : Nat)

private def coefficient (x : Q 9) : Int :=
  (∑ i : Fin 9, (upper (flip x i) - lower (flip x i))) +
    upper x * (cap x - 3) + 3 * lower x + box x

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the integer coefficient at each allowed cube vertex.
private theorem coefficient_bound : ∀ x : Q 9, B x = true → 576 ≤ coefficient x := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Evaluate the sum of certificate right-hand sides over the full cube.
private theorem total_bound : (∑ x : Q 9, (upper x * cap x + box x)) = 89280 := by
  decide +kernel

private def indicator (D : Finset (Q 9)) (x : Q 9) : Int := if x ∈ D then 1 else 0

private def degreeInto (D : Finset (Q 9)) (x : Q 9) : Int :=
  ∑ i : Fin 9, indicator D (flip x i)

private theorem degreeInto_eq (D : Finset (Q 9)) (x : Q 9) :
    degreeInto D x = ((directions D x).card : Int) := by
  simp [degreeInto, indicator, directions]

open Classical in
private theorem vertex_inequalities {D : Finset (Q 9)}
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) (hD : ∀ x ∈ D, B x = true) (x : Q 9) :
    degreeInto D x + (cap x - 3) * indicator D x ≤ cap x ∧
      3 * indicator D x - degreeInto D x ≤ 0 ∧ indicator D x ≤ 1 := by
  by_cases hx : x ∈ D
  · have hdeg := regular_directions D hr hx
    simp [degreeInto_eq, hdeg, indicator, hx]
  · obtain ⟨k, hk⟩ := exterior_even D hr hb x hx
    have hle := Finset.card_le_card (directions_subset hD x)
    simp only [degreeInto_eq, indicator, ite_eq_right hx, mul_zero, add_zero, zero_sub]
    unfold cap
    omega

private theorem transfer_flips (w f : Q 9 → Int) :
    (∑ x, w x * (∑ i : Fin 9, f (flip x i))) =
      ∑ x, (∑ i : Fin 9, w (flip x i)) * f x := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Q 9))),
    Finset.sum_comm (s := (Finset.univ : Finset (Q 9)))]
  apply Finset.sum_congr rfl
  intro i _
  have hinv : Function.Involutive (fun x : Q 9 => flip x i) :=
    fun x => BalancedCriticalSpectrum.flip_flip x i
  calc
    (∑ x, w x * f (flip x i)) =
        ∑ x, w (flip x i) * f (flip (flip x i) i) :=
      (hinv.bijective.sum_comp (fun x => w x * f (flip x i))).symm
    _ = _ := by simp only [BalancedCriticalSpectrum.flip_flip]

open Classical in
private theorem weighted_bound {D : Finset (Q 9)}
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) (hD : ∀ x ∈ D, B x = true) :
    (∑ x, coefficient x * indicator D x) ≤ 89280 := by
  let I := indicator D
  let d := degreeInto D
  have hlocal (x : Q 9) :
      upper x * (d x + (cap x - 3) * I x) +
        lower x * (3 * I x - d x) + box x * I x ≤ upper x * cap x + box x := by
    obtain ⟨hu, hl, hc⟩ := vertex_inequalities hr hb hD x
    have hu' : upper x * (d x + (cap x - 3) * I x) ≤ upper x * cap x :=
      mul_le_mul_of_nonneg_left hu (Int.natCast_nonneg _)
    have hl' : lower x * (3 * I x - d x) ≤ lower x * 0 :=
      mul_le_mul_of_nonneg_left hl (Int.natCast_nonneg _)
    have hc' : box x * I x ≤ box x * 1 :=
      mul_le_mul_of_nonneg_left hc (Int.natCast_nonneg _)
    rw [mul_zero] at hl'
    rw [mul_one] at hc'
    exact add_le_add (add_le_add hu' hl') hc' |>.trans_eq (by rw [add_zero])
  calc
    (∑ x, coefficient x * I x) =
        (∑ x, (∑ i : Fin 9, (upper (flip x i) - lower (flip x i))) * I x) +
          ∑ x, (upper x * (cap x - 3) + 3 * lower x + box x) * I x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      unfold coefficient
      ring
    _ = (∑ x, (upper x - lower x) * d x) +
          ∑ x, (upper x * (cap x - 3) + 3 * lower x + box x) * I x := by
      congr 1
      exact (transfer_flips (fun x => upper x - lower x) I).symm
    _ = ∑ x, (upper x * (d x + (cap x - 3) * I x) +
          lower x * (3 * I x - d x) + box x * I x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, (upper x * cap x + box x) := Finset.sum_le_sum fun x _ => hlocal x
    _ = 89280 := total_bound

open Classical in
/-- Every separated induced cubic Huang-balanced partner of the explicit star
has at most 150 vertices. -/
theorem partner_card_le_150 (D : Finset (Q 9))
    (hdisj : Disjoint Sstar D)
    (hcross : ∀ s ∈ Sstar, ∀ d ∈ D, ¬ (hypercube 9).Adj s d)
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) : D.card ≤ 150 := by
  have hD := partner_subset_B hr hb (fun _ => eligible_of_separated hdisj hcross)
  have hcard : (576 : Int) * D.card ≤ 89280 := by
    calc
      (576 : Int) * D.card = ∑ x ∈ D, (576 : Int) := by simp [mul_comm]
      _ ≤ ∑ x ∈ D, coefficient x := Finset.sum_le_sum fun x hx =>
        coefficient_bound x (hD x hx)
      _ = ∑ x, coefficient x * indicator D x := by
        simp only [indicator, mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
          Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ ≤ 89280 := weighted_bound hr hb hD
  have hdiv := direction_edge_count (d := 3) D hr hb (0 : Fin 9)
  omega

#print axioms star_card
#print axioms forced_exclusion
#print axioms coefficient_bound
#print axioms total_bound
#print axioms partner_card_le_150

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerBound
