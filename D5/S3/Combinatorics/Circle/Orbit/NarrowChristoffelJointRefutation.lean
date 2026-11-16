/- GID: D5/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.Orbit.NarrowDoublingOrbit, lake/module/D5.S3.Combinatorics.Circle.RunFirstEarTransport]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation.claim; result=D5/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation.result; claim=D5/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation.claim
   digest: The complete primitive anchored-seed joint physical-order assertion is false at r=5,s=2,u=3; the native source values are checked by a kernel finite enumeration of all original orders and all fresh cuts. -/

import D5.S3.Combinatorics.Circle.Orbit.NarrowDoublingOrbit
import D5.S3.Combinatorics.Circle.RunFirstEarTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.NarrowChristoffelJointRefutation

open D5.S3.Combinatorics.Circle.SourceWidth
open D5.S3.Combinatorics.Circle.PeriodicShortening
open D5.S3.Combinatorics.Circle.RunFirstEarTransport
open D5.S3.Combinatorics.Circle.NarrowDoublingOrbit

/- The complete physical assertion: the same permutation of all original
   physical labels must work before and after inserting one fresh label. -/
def claim : Prop :=
  ∀ r s u : ℕ, 2 ≤ r → 0 < s → s < r → Nat.Coprime r s →
    0 < u → u < r → (s : ZMod r) * u = 1 →
    ∃ sigma : List (Fin r), ∃ cut : ℕ,
      cut ≤ r ∧
      OriginalOrder r (explicitNumerator r s u) sigma ∧
      OriginalOrder (r + 1) (2 * explicitNumerator r s u)
        (earWord r sigma cut)

/- These are the finite prefix predicates used by the kernel enumeration.
   `OriginalOrder` quantifies over all natural prefix lengths; for a word of
   length 5 (respectively 6), Fin 6 (respectively Fin 7) contains every
   nontrivial prefix length, including the full word. -/
private def oldPrefixOK (sigma : List (Fin 5)) : Bool :=
  (List.finRange 6).all (fun h =>
    decide (((sigma.take h.val).map (actualSource 5 20)).sum ∈
      Set.Icc (0 : ℤ) (modulus 5 / 2)))

private def newPrefixOK (word : List (Fin 6)) : Bool :=
  (List.finRange 7).all (fun h =>
    decide (((word.take h.val).map (actualSource 6 40)).sum ∈
      Set.Icc (0 : ℤ) (modulus 6 / 2)))

/- A Boolean finite check is used so that `decide` enumerates only the finite
   list of 5-permutations and the six possible cuts.  It uses the native
   `actualSource`, `modulus`, and `earWord` definitions directly. -/
private def finiteObstruction : Bool :=
  (List.finRange 5).permutations.all (fun sigma =>
    (List.finRange 6).all (fun cut =>
      decide (¬ (oldPrefixOK sigma = true ∧
        newPrefixOK (earWord 5 sigma cut.val) = true))))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem finiteObstruction_true : finiteObstruction = true := by
  simp only [finiteObstruction,
    show List.finRange 5 = ([0,1,2,3,4] : List (Fin 5)) from rfl,
    List.permutations, List.permutationsAux_cons, List.permutationsAux_nil]
  decide +kernel

/- The Boolean certificate covers an arbitrary sigma because an
   `OriginalOrder` permutation is a member of the finite permutation list. -/
private theorem finiteObstruction_spec (sigma : List (Fin 5))
    (hsigma : sigma ∈ (List.finRange 5).permutations) (cut : Fin 6)
    (hcut : cut ∈ List.finRange 6) :
    decide (¬ (oldPrefixOK sigma = true ∧
      newPrefixOK (earWord 5 sigma cut.val) = true)) = true := by
  have h := finiteObstruction_true
  simp only [finiteObstruction] at h
  have hp := (List.all_eq_true.mp h) sigma hsigma
  exact (List.all_eq_true.mp hp) cut hcut

theorem result : ¬ claim := by
  intro hclaim
  have h5 := hclaim 5 2 3
    (by norm_num : 2 ≤ 5)
    (by norm_num : 0 < 2)
    (by norm_num : 2 < 5)
    (by norm_num : Nat.Coprime 5 2)
    (by norm_num : 0 < 3)
    (by norm_num : 3 < 5)
    (by decide +kernel : (2 : ZMod 5) * 3 = 1)
  have hQ : explicitNumerator 5 2 3 = 20 := by
    decide +kernel
  have h5' :
      ∃ sigma : List (Fin 5), ∃ cut : ℕ,
        cut ≤ 5 ∧ OriginalOrder 5 20 sigma ∧
          OriginalOrder 6 40 (earWord 5 sigma cut) := by
    simpa [hQ] using h5
  rcases h5' with ⟨sigma, cut, hcut, hold, hnew⟩
  let c : Fin 6 := ⟨cut, by omega⟩
  have hsigma : sigma ∈ (List.finRange 5).permutations := by
    exact List.mem_permutations.mpr hold.1
  have holdOK : oldPrefixOK sigma = true := by
    simp only [oldPrefixOK, List.all_eq_true, decide_eq_true_eq]
    intro n _
    exact hold.2.2 n.val
  have hnewOK : newPrefixOK (earWord 5 sigma c.val) = true := by
    simp only [newPrefixOK, List.all_eq_true, decide_eq_true_eq]
    intro n _
    exact hnew.2.2 n.val
  have hbad := finiteObstruction_spec sigma hsigma c (by simp)
  exact (of_decide_eq_true hbad) ⟨holdOK, hnewOK⟩

end D5.S3.Combinatorics.Circle.NarrowChristoffelJointRefutation
