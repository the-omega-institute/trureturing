/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeKernelSupport]
   utility: none
   digest: Sharp opposite-section sums are disjoint within each pair and attain the six-cube minimum. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeKernelSupport

/-! Equality in the two-coordinate split budget forces both opposite
section sums to be minimum-weight six-cube kernel words, with no
cancellation within either opposite pair. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSharpSplit

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency adjacency_opposite_sections_zero)
open BinaryCubeKernelSupport (binarySites add_sites_card_add_twice_inter)

/-- Section obtained by fixing the first two coordinates. -/
def twoSection {n : ℕ} (f : Q (n + 2) → ZMod 2) (a b : Bool) : Q n → ZMod 2 :=
  fun x => f (Fin.cons a (Fin.cons b x))

private theorem sites_card_halves {n : ℕ} (f : Q (n + 1) → ZMod 2) :
    (binarySites f).card =
      (binarySites (fun x : Q n => f (Fin.cons false x))).card +
      (binarySites (fun x : Q n => f (Fin.cons true x))).card := by
  classical
  unfold binarySites
  calc
    _ = ∑ x : Q (n+1), if f x ≠ 0 then (1 : ℕ) else 0 :=
      (Finset.sum_boole (R := ℕ) (fun x : Q (n+1) => f x ≠ 0) univ).symm
    _ = (∑ x : Q n, if f (Fin.cons false x) ≠ 0 then (1 : ℕ) else 0) +
        (∑ x : Q n, if f (Fin.cons true x) ≠ 0 then (1 : ℕ) else 0) := by
      have h := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool))
        (fun x : Q (n+1) => if f x ≠ 0 then (1 : ℕ) else 0)
      rw [← h, Fintype.sum_prod_type]
      simp only [Fin.consEquiv_apply, Fintype.univ_bool,
        sum_insert (by decide : true ∉ ({false} : Finset Bool)), sum_singleton]
      ac_rfl
    _ = _ := congrArg₂ (· + ·)
      (Finset.sum_boole (R := ℕ) (fun x : Q n => f (Fin.cons false x) ≠ 0) univ)
      (Finset.sum_boole (R := ℕ) (fun x : Q n => f (Fin.cons true x) ≠ 0) univ)

/-- Support size is the sum of the four section sizes. -/
theorem sites_card_two_sections {n : ℕ} (f : Q (n + 2) → ZMod 2) :
    (binarySites f).card =
      (binarySites (twoSection f false false)).card +
      (binarySites (twoSection f true true)).card +
      ((binarySites (twoSection f true false)).card +
       (binarySites (twoSection f false true)).card) := by
  unfold twoSection
  rw [sites_card_halves f, sites_card_halves (fun x : Q (n+1) => f (Fin.cons false x)),
    sites_card_halves (fun x : Q (n+1) => f (Fin.cons true x))]
  omega

private theorem six_le_weight (g : Q 6 → ZMod 2)
    (hg : adjacency g = 0) (hne : g ≠ 0) : 6 ≤ (binarySites g).card := by
  by_cases hw : (binarySites g).card ≤ 6
  · obtain ⟨_, h, _⟩ :=
      BinaryCubeKernelSupport.minimum_kernel_support (n := 6) (by decide) (by decide) g hg hne hw
    exact Nat.le_of_eq h.symm
  · omega

/-- For a Q8 binary adjacency kernel word of weight at most twelve,
if both opposite section sums are nonzero, the weight is twelve, the
two sums are six-cube neighborhood indicators, and opposite sections
have disjoint support. -/
theorem sharp_split (f : Q 8 → ZMod 2) (hf : adjacency f = 0)
    (hw : (binarySites f).card ≤ 12)
    (hu : twoSection f false false + twoSection f true true ≠ 0)
    (hv : twoSection f true false + twoSection f false true ≠ 0) :
    (binarySites f).card = 12 ∧
    (∃ p : Q 6, binarySites (twoSection f false false + twoSection f true true) =
      univ.image (BalancedCriticalSpectrum.flip p)) ∧
    (∃ q : Q 6, binarySites (twoSection f true false + twoSection f false true) =
      univ.image (BalancedCriticalSpectrum.flip q)) ∧
    Disjoint (binarySites (twoSection f false false)) (binarySites (twoSection f true true)) ∧
    Disjoint (binarySites (twoSection f true false)) (binarySites (twoSection f false true)) := by
  let a := twoSection f false false
  let d := twoSection f true true
  let b := twoSection f true false
  let c := twoSection f false true
  have hkeru : adjacency (a + d) = 0 := adjacency_opposite_sections_zero hf false false
  have hkerv : adjacency (b + c) = 0 := adjacency_opposite_sections_zero hf true false
  have hlu := six_le_weight (a+d) hkeru hu
  have hlv := six_le_weight (b+c) hkerv hv
  have hcount : (binarySites f).card =
      (binarySites a).card + (binarySites d).card +
      ((binarySites b).card + (binarySites c).card) := sites_card_two_sections f
  have hU := add_sites_card_add_twice_inter a d
  have hV := add_sites_card_add_twice_inter b c
  have htotal : (binarySites f).card = 12 := by omega
  have hwu : (binarySites (a+d)).card ≤ 6 := by omega
  have hwv : (binarySites (b+c)).card ≤ 6 := by omega
  have hdisu : Disjoint (binarySites a) (binarySites d) := by
    rw [disjoint_iff_inter_eq_empty, ← card_eq_zero]
    omega
  have hdisv : Disjoint (binarySites b) (binarySites c) := by
    rw [disjoint_iff_inter_eq_empty, ← card_eq_zero]
    omega
  obtain ⟨p, _, hp⟩ := BinaryCubeKernelSupport.minimum_kernel_support (n := 6)
    (by decide) (by decide) (a+d) hkeru hu hwu
  obtain ⟨q, _, hq⟩ := BinaryCubeKernelSupport.minimum_kernel_support (n := 6)
    (by decide) (by decide) (b+c) hkerv hv hwv
  exact ⟨htotal, ⟨p,hp⟩, ⟨q,hq⟩, hdisu, hdisv⟩

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSharpSplit.sharp_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sharp_split

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSharpSplit
