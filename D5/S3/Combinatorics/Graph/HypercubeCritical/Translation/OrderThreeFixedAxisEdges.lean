/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/OrderThreeFixedAxisEdges
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/Translation/OrderThreeFixedAxisEdges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Order-three edge orbits and a translation period force a multiple of thirty-six in Q9. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
import Mathlib.GroupTheory.Perm.Cycle.Type
import Batteries.Tactic.OpenPrivate

/-! A fixed-axis edge of a balanced cubic support cannot meet a fixed vertex of
a cube symmetry whose axis permutation has order dividing three and fixes at most
three axes. The order-three action on such edges then gives a divisibility obstruction. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.OrderThreeFixedAxisEdges

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj IsBalanced directionEdges)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open BalancedCubeGirth (no_selected_square)
open private translate translate_translate translate_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private theorem apply_three {α : Type*} (p : Equiv.Perm α) (hp : p ^ 3 = 1) (x : α) :
    p (p (p x)) = x := by
  simpa only [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
    congrArg (fun q : Equiv.Perm α => q x) hp

private theorem directions_eq_fixed_axes {n : ℕ} (p : Equiv.Perm (Fin n))
    (hp : p ^ 3 = 1) (hfixed : (Finset.univ.filter fun j => p j = j).card ≤ 3)
    {D : Finset (Fin n)} (hD : D.card = 3) (hmap : ∀ j ∈ D, p j ∈ D)
    {i : Fin n} (hi : i ∈ D) (hpi : p i = i) :
    D = Finset.univ.filter (fun j => p j = j) := by
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hjm
    have hij : i ≠ j := by
      intro h
      subst j
      exact hjm hpi
    have hipj : i ≠ p j := fun h => hij (p.injective (hpi.trans h))
    have hippj : i ≠ p (p j) := fun h => hipj (p.injective (hpi.trans h))
    have hjpj : j ≠ p j := fun h => hjm h.symm
    have hjppj : j ≠ p (p j) := fun h =>
      hjm ((congrArg (fun k => p k) h).trans (apply_three p hp j))
    have hpjppj : p j ≠ p (p j) := fun h => hjpj (p.injective h)
    let T : Finset (Fin n) := {i, j, p j, p (p j)}
    have hT : T ⊆ D := by
      intro k hk
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hmap j hj
      · exact hmap (p j) (hmap j hj)
    have hcard : T.card = 4 := by
      simp [T, hij, hipj, hippj, hjpj, hjppj, hpjppj]
    have hle := Finset.card_le_card hT
    omega
  · rw [hD]
    exact hfixed

open Classical in
/-- A selected edge in an individually fixed axis has no fixed endpoint.
The order hypothesis is only needed on the axis permutation. -/
private theorem fixed_axis_endpoint_not_fixed {n : ℕ} {C : Finset (Q n)}
    (hbal : IsBalanced C) (hreg : ((hypercube n).induce (C : Set (Q n))).IsRegularOfDegree 3)
    (g : Equiv.Perm (Q n)) (p : Equiv.Perm (Fin n))
    (hp : p ^ 3 = 1) (hfixed : (Finset.univ.filter fun j => p j = j).card ≤ 3)
    (hflip : ∀ x j, g (cubeFlip x j) = cubeFlip (g x) (p j))
    (hCmap : ∀ x ∈ C, g x ∈ C)
    {x : Q n} {i : Fin n} (hi : p i = i) (hx : x ∈ C) (hxi : cubeFlip x i ∈ C) :
    g x ≠ x := by
  intro hgx
  have hgxi : g (cubeFlip x i) = cubeFlip x i := by rw [hflip, hgx, hi]
  have hmap {y : Q n} (hgy : g y = y) (j : Fin n) (hj : j ∈ directions C y) :
      p j ∈ directions C y := by
    apply (mem_directions C y (p j)).mpr
    simpa only [hflip, hgy] using hCmap _ ((mem_directions C y j).mp hj)
  have hix : i ∈ directions C x := (mem_directions C x i).mpr hxi
  have hiy : i ∈ directions C (cubeFlip x i) :=
    (mem_directions C (cubeFlip x i) i).mpr (by
      simpa only [BalancedCriticalSpectrum.flip_flip] using hx)
  have hcard := regular_directions C hreg hx
  have hDx := directions_eq_fixed_axes p hp hfixed hcard (hmap hgx) hix hi
  have hDy := directions_eq_fixed_axes p hp hfixed
    (regular_directions C hreg hxi) (hmap hgxi) hiy hi
  have hone : 1 < (directions C x).card := by omega
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hone i
  have hjy : j ∈ directions C (cubeFlip x i) := by rwa [hDy, ← hDx]
  exact no_selected_square hbal hji.symm hx hxi ((mem_directions C x j).mp hj)
    ((mem_directions C (cubeFlip x i) j).mp hjy)

open Classical in
/-- The false-parity endpoints represent the selected edges in a fixed axis.
Applying the symmetry and reorienting gives a permutation of order dividing three.
A fixed representative would force its endpoints to be fixed or swapped. -/
theorem three_dvd_directionEdges {n : ℕ} {C : Finset (Q n)}
    (hbal : IsBalanced C) (hreg : ((hypercube n).induce (C : Set (Q n))).IsRegularOfDegree 3)
    (g : Equiv.Perm (Q n)) (p : Equiv.Perm (Fin n))
    (hg : g ^ 3 = 1) (hp : p ^ 3 = 1)
    (hfixed : (Finset.univ.filter fun j => p j = j).card ≤ 3)
    (hflip : ∀ x j, g (cubeFlip x j) = cubeFlip (g x) (p j))
    (hCmap : ∀ x ∈ C, g x ∈ C) {i : Fin n} (hi : p i = i) :
    3 ∣ directionEdges C i := by
  classical
  let E := C.filter (fun x => cubeParity x = false ∧ cubeFlip x i ∈ C)
  let F := C.filter (fun x => x i = false ∧ cubeFlip x i ∈ C)
  let orient (x : Q n) : Q n := if cubeParity x = false then x else cubeFlip x i
  let orientCoord (x : Q n) : Q n := if x i = false then x else cubeFlip x i
  have hpar (x : Q n) : cubeParity (cubeFlip x i) = !cubeParity x :=
    (Bool.not_eq_iff.mpr (cubeParity_ne_of_adj (flip_adj x i))).symm
  have horientFlip (x : Q n) : orient (cubeFlip x i) = orient x := by
    cases h : cubeParity x <;> simp [orient, hpar, h]
  have horientMem {x : Q n} (hx : x ∈ C) (hxi : cubeFlip x i ∈ C) : orient x ∈ E := by
    cases h : cubeParity x <;> simp [E, orient, hx, hxi, hpar, h]
  have hcard : F.card = E.card := by
    apply Finset.card_bij' (fun x _ => orient x) (fun y _ => orientCoord y)
    · intro x hx
      exact horientMem (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2.2
    · intro y hy
      have hyC : y ∈ C := (Finset.mem_filter.mp hy).1
      have hyI : cubeFlip y i ∈ C := (Finset.mem_filter.mp hy).2.2
      cases h : y i <;> simp [F, orientCoord, h, hyC, hyI]
    · intro x hx
      have hxi : x i = false := (Finset.mem_filter.mp hx).2.1
      by_cases h : cubeParity x = false <;> simp [orientCoord, orient, h, hxi]
    · intro y hy
      have hyP : cubeParity y = false := (Finset.mem_filter.mp hy).2.1
      cases h : y i <;> simp [orientCoord, h, orient, hpar, hyP]
  have hcomm (x : Q n) : g (cubeFlip x i) = cubeFlip (g x) i := by rw [hflip, hi]
  have hreduce (x : Q n) : orient (g (orient x)) = orient (g x) := by
    by_cases h : cubeParity x = false
    · have he : orient x = x := ite_eq_left h
      rw [he]
    · have he : orient x = cubeFlip x i := ite_eq_right h
      rw [he, hcomm, horientFlip]
  let step : E → E := fun x =>
    ⟨orient (g x.1), horientMem (hCmap _ (Finset.mem_filter.mp x.2).1) (by
      rw [← hcomm]
      exact hCmap _ (Finset.mem_filter.mp x.2).2.2)⟩
  have hstep (x : E) : step (step (step x)) = x := by
    apply Subtype.ext
    change orient (g (orient (g (orient (g x.1))))) = x.1
    rw [hreduce (g x.1), hreduce (g (g x.1)), apply_three g hg]
    exact ite_eq_left (Finset.mem_filter.mp x.2).2.1
  let σ : Equiv.Perm E := ⟨step, fun x => step (step x), hstep, hstep⟩
  have hσ : σ ^ 3 = 1 := Equiv.ext fun x => by
    simpa only [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      using (show σ (σ (σ x)) = x from hstep x)
  change 3 ∣ F.card
  rw [hcard, ← Fintype.card_coe E]
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  by_contra hndvd
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) (σ := σ) hndvd
    (by simpa only [pow_one] using hσ)
  have heq : orient (g x.1) = x.1 := congrArg Subtype.val hx
  have hmove := fixed_axis_endpoint_not_fixed hbal hreg g p hp hfixed hflip hCmap hi
    (Finset.mem_filter.mp x.2).1 (Finset.mem_filter.mp x.2).2.2
  by_cases h : cubeParity (g x.1) = false
  · exact hmove (by simpa only [orient, ite_eq_left h] using heq)
  · have hflipEq : cubeFlip (g x.1) i = x.1 := by simpa only [orient, ite_eq_right h] using heq
    have hswap : g x.1 = cubeFlip x.1 i := by
      simpa only [BalancedCriticalSpectrum.flip_flip] using congrArg (fun z => cubeFlip z i) hflipEq
    have hswap' : g (g x.1) = x.1 := by
      calc
        g (g x.1) = g (cubeFlip x.1 i) := congrArg (fun z => g z) hswap
        _ = cubeFlip (g x.1) i := hcomm _
        _ = x.1 := hflipEq
    exact hmove (by simpa only [hswap'] using apply_three g hg x.1)

open Classical in
private theorem two_dvd_directionEdges_of_involution {n : ℕ} {C : Finset (Q n)}
    (i : Fin n) (t : Q n → Q n) (ht : Function.Involutive t)
    (hcomm : ∀ x, t (cubeFlip x i) = cubeFlip (t x) i)
    (hCmap : ∀ x ∈ C, t x ∈ C)
    (hfree : ∀ x, t x ≠ x ∧ t x ≠ cubeFlip x i) :
    2 ∣ directionEdges C i := by
  let E := C.filter (fun x => x i = false ∧ cubeFlip x i ∈ C)
  let orient (x : Q n) : Q n := if x i = false then x else cubeFlip x i
  have horientFlip (x : Q n) : orient (cubeFlip x i) = orient x := by
    cases h : x i <;> simp [orient, h, BalancedCriticalSpectrum.flip_flip]
  have horientMem {x : Q n} (hx : x ∈ C) (hxi : cubeFlip x i ∈ C) : orient x ∈ E := by
    cases h : x i <;> simp [E, orient, h, hx, hxi, BalancedCriticalSpectrum.flip_flip]
  have hreduce (x : Q n) : orient (t (orient x)) = orient (t x) := by
    by_cases h : x i = false
    · have he : orient x = x := ite_eq_left h
      rw [he]
    · have he : orient x = cubeFlip x i := ite_eq_right h
      rw [he, hcomm, horientFlip]
  let step : E → E := fun x =>
    ⟨orient (t x.1), horientMem (hCmap _ (Finset.mem_filter.mp x.2).1) (by
      rw [← hcomm]
      exact hCmap _ (Finset.mem_filter.mp x.2).2.2)⟩
  have step_sq (x : E) : step (step x) = x := by
    apply Subtype.ext
    change orient (t (orient (t x.1))) = x.1
    rw [hreduce (t x.1), ht x.1]
    exact ite_eq_left (Finset.mem_filter.mp x.2).2.1
  let σ : Equiv.Perm E := ⟨step, step, step_sq, step_sq⟩
  have hσ : σ ^ 2 = 1 := Equiv.ext fun x => by
    simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      using (show σ (σ x) = x from step_sq x)
  change 2 ∣ E.card
  rw [← Fintype.card_coe E]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hndvd
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) (σ := σ) hndvd
    (by simpa only [pow_one] using hσ)
  have heq : orient (t x.1) = x.1 := congrArg Subtype.val hx
  by_cases h : t x.1 i = false
  · exact (hfree x.1).1 (by simpa only [orient, ite_eq_left h] using heq)
  · have he : cubeFlip (t x.1) i = x.1 := by
      simpa only [orient, ite_eq_right h] using heq
    exact (hfree x.1).2 (by
      simpa only [BalancedCriticalSpectrum.flip_flip] using congrArg (fun x => cubeFlip x i) he)

open Classical in
/-- A fixed axis for the order-three action and a translation period moving another axis
force a balanced cubic nine-cube support to have size divisible by thirty-six. -/
theorem thirtySix_dvd_card_of_fixed_axis_and_period {C : Finset (Q 9)}
    (hbal : IsBalanced C) (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (g : Equiv.Perm (Q 9)) (p : Equiv.Perm (Fin 9))
    (hg : g ^ 3 = 1) (hp : p ^ 3 = 1)
    (hfixed : (Finset.univ.filter fun j => p j = j).card ≤ 3)
    (hflip : ∀ x j, g (cubeFlip x j) = cubeFlip (g x) (p j))
    (hCmap : ∀ x ∈ C, g x ∈ C) {i : Fin 9} (hi : p i = i)
    (a : Q 9) (hperiod : ∀ x ∈ C, (fun j => Bool.xor (a j) (x j)) ∈ C)
    (hother : ∃ j ≠ i, a j = true) :
    36 ∣ C.card := by
  obtain ⟨j, hji, haj⟩ := hother
  have hfree (x : Q 9) : translate a x ≠ x ∧ translate a x ≠ cubeFlip x i := by
    have hcoord : translate a x j ≠ x j := by
      cases hx : x j <;> simp [translate, haj, hx]
    refine ⟨fun h => hcoord (congrFun h j), ?_⟩
    intro h
    apply hcoord
    simpa only [BalancedCriticalSpectrum.flip, Function.update_of_ne hji] using congrFun h j
  have hthree := three_dvd_directionEdges hbal hreg g p hg hp hfixed hflip hCmap hi
  have htwo := two_dvd_directionEdges_of_involution i (translate a) (translate_translate a)
    (fun x => translate_flip a x i) hperiod hfree
  obtain ⟨k, hk⟩ := (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd htwo hthree
  have hcount := BalancedCriticalSpectrum.direction_edge_count (d := 3) C hreg hbal i
  exact ⟨k, by omega⟩

/-!
For `Q 9`, `BalancedCriticalSpectrum.direction_edge_count` gives
`6 * directionEdges C i = C.card` from balance and cubicity.
A nonzero even XOR translation period pairs edges of any given axis. A fixed
edge would require the translation mask to be zero or the singleton of that
axis, since the translated endpoint must be one of the original endpoints.
If the support is also stabilized by a cube symmetry with cube equal to the
identity and axis permutation `(012)(345)`, each fixed axis has edge count
divisible by both two and three. Thus `36 ∣ C.card`, and in the inclusive
range 66–144 the only remaining sizes are 72, 108, and 144.
-/

end D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.OrderThreeFixedAxisEdges
