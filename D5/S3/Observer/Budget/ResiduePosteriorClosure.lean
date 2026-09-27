/- GID: D5/S3/Observer/Budget/ResiduePosteriorClosure
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ResiduePosteriorClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual residue histories have exact sibling fibers and positive rational posteriors. -/

import D5.S3.Observer.Budget.ResidueLeafOptimality
import D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution
import D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.GroupTheory.Index

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Observer.Budget.ResidueLeafOptimality
open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
namespace D5.S3.Observer.Budget.ResiduePosteriorClosure

/-- A complete projection fiber at a specified depth. -/
def node (p e d : ℕ) [NeZero p] (hd : d ≤ e) (b : ZMod (p ^ d)) :
    Finset (ZMod (p ^ e)) := Finset.univ.filter (fun a => primePowerProjection p hd a = b)

/-- All next-depth residue labels over the parent label. -/
def children (p d : ℕ) [NeZero p] (b : ZMod (p ^ d)) : Finset (ZMod (p ^ (d + 1))) :=
  node p (d + 1) d (Nat.le_succ d) b

/-- The union of the complete child fibers indexed by the active labels. -/
def siblings (p e d : ℕ) [NeZero p] (hd : d < e) (I : Finset (ZMod (p ^ (d + 1)))) :
    Finset (ZMod (p ^ e)) :=
  Finset.univ.filter (fun a => primePowerProjection p (Nat.succ_le_of_lt hd) a ∈ I)

/-- A nonempty state is a singleton or a union of children from one parent. -/
def stateShape (p e : ℕ) [NeZero p] (S : Finset (ZMod (p ^ e))) : Prop :=
  (∃ a, S = {a}) ∨ ∃ (d : ℕ) (hd : d < e) (b : ZMod (p ^ d))
    (I : Finset (ZMod (p ^ (d + 1)))), I.Nonempty ∧ I ⊆ children p d b ∧ S = siblings p e d hd I

/-- Unroll a selector on its full chronological history into the existing protocol. -/
def unroll {X : Type} (D : List (X × ℕ) → Option X) :
    ℕ → List (X × ℕ) → PassiveProtocol X (fun _ => ℕ)
  | 0, _ => .stop
  | n + 1, H => match D H with
    | none => .stop
    | some c => .query c (fun r => unroll D n (H ++ [(c,r)]))

/-- Policy legality tests each selected center against precisely its earlier history. -/
def legal {X : Type} (D : List (X × ℕ) → Option X) (P : List (X × ℕ)) : List (X × ℕ) → Prop
  | [] => True
  | (c,r)::H => D P = some c ∧ legal D (P ++ [(c,r)]) H

/-- Logical candidates depend only on the recorded readout equations. -/
def candidates (p e : ℕ) [NeZero p] (H : List (ZMod (p ^ e) × ℕ)) : Finset (ZMod (p ^ e)) :=
  Finset.univ.filter (fun a => ∀ z ∈ H, residueReadout p e z.1 a = z.2)

/-- The observed event is defined by actual protocol execution, before
any candidate identification. -/
def actualEvent (p e : ℕ) [NeZero p] (D : List (ZMod (p ^ e) × ℕ) → Option (ZMod (p ^ e)))
    (H : List (ZMod (p ^ e) × ℕ)) : Finset (ZMod (p ^ e)) :=
  Finset.univ.filter (fun a =>
    (runPassiveProtocol (residueReadout p e) (unroll D H.length []) a).map
      (fun z => (z.1,z.2)) = H)

/-- Exact residue - query fibers, chronological execution events, and conditional
posterior closure for every strictly positive rational prior. -/
theorem residue_posterior_closure (p e : ℕ) [Fact p.Prime]
    (μ : ZMod (p ^ e) → ℚ) (positive : ∀ a, 0 < μ a) (normalized : ∑ a, μ a = 1) :
    (∀ (k : ℕ) (hk : k ≤ e) (a c : ZMod (p ^ e)),
      k ≤ residueReadout p e c a ↔ primePowerProjection p hk a = primePowerProjection p hk c) ∧
    (∀ (t : ℕ) (ht : t < e) (a c : ZMod (p ^ e)), residueReadout p e c a = t ↔
      primePowerProjection p (Nat.le_of_lt ht) a = primePowerProjection p (Nat.le_of_lt ht) c ∧
      primePowerProjection p (Nat.succ_le_of_lt ht) a ≠
        primePowerProjection p (Nat.succ_le_of_lt ht) c) ∧
    (∀ a c : ZMod (p ^ e), residueReadout p e c a = e ↔ a = c) ∧
    (∀ (d : ℕ) (hd : d ≤ e) (b : ZMod (p ^ d)), (node p e d hd b).card = p ^ (e - d)) ∧
    (∀ (d : ℕ) (hd : d < e) (b : ZMod (p ^ d)), (children p d b).card = p ∧
      (children p d b).biUnion (node p e (d + 1) (Nat.succ_le_of_lt hd)) =
        node p e d (Nat.le_of_lt hd) b ∧
      (∀ j k : ZMod (p ^ (d + 1)), j ≠ k → Disjoint
        (node p e (d + 1) (Nat.succ_le_of_lt hd) j) (node p e (d + 1) (Nat.succ_le_of_lt hd) k)) ∧
      (∀ I : Finset (ZMod (p ^ (d + 1))), siblings p e d hd I =
        I.biUnion (node p e (d + 1) (Nat.succ_le_of_lt hd)))) ∧
    (∀ (d : ℕ) (hd : d < e) (b : ZMod (p ^ d)) (I : Finset (ZMod (p ^ (d + 1)))),
      I ⊆ children p d b → ∀ c : ZMod (p ^ e),
      (∀ a ∈ siblings p e d hd I, a ∈ node p e d (Nat.le_of_lt hd) b) ∧
      (c ∈ node p e d (Nat.le_of_lt hd) b → c ∉ siblings p e d hd I →
        ∀ a ∈ siblings p e d hd I, residueReadout p e c a = d) ∧
      (c ∉ node p e d (Nat.le_of_lt hd) b → ∀ b0 ∈ node p e d (Nat.le_of_lt hd) b,
        residueReadout p e c b0 < d ∧ ∀ a ∈ node p e d (Nat.le_of_lt hd) b,
          residueReadout p e c a = residueReadout p e c b0) ∧
      (c ∈ siblings p e d hd I →
        ((siblings p e d hd I).filter (fun a => residueReadout p e c a = d) =
          siblings p e d hd (I.erase (primePowerProjection p (Nat.succ_le_of_lt hd) c))) ∧
        (∀ t (_hdt : d < t) (hte : t < e),
          (siblings p e d hd I).filter (fun a => residueReadout p e c a = t) =
            siblings p e t hte ((children p t (primePowerProjection p (Nat.le_of_lt hte) c)).erase
              (primePowerProjection p (Nat.succ_le_of_lt hte) c))) ∧
        ((siblings p e d hd I).filter (fun a => residueReadout p e c a = e) = {c}) ∧
        (∀ r, r < d ∨ e < r →
          (siblings p e d hd I).filter (fun a => residueReadout p e c a = r) = ∅) ∧
        (((siblings p e d hd I).filter (fun a => residueReadout p e c a = d)).Nonempty ↔
          (I.erase (primePowerProjection p (Nat.succ_le_of_lt hd) c)).Nonempty))) ∧
    (∀ (d : ℕ) (hd : d < e) (b : ZMod (p ^ d)) (I : Finset (ZMod (p ^ (d + 1)))),
      I.Nonempty → I ⊆ children p d b → ∀ c : ZMod (p ^ e), c ∉ siblings p e d hd I →
      ∃ r ≤ e, ∀ t, (siblings p e d hd I).filter (fun a => residueReadout p e c a = t) =
        if t = r then siblings p e d hd I else ∅) ∧
    (∀ (t : ℕ) (ht : t < e) (c : ZMod (p ^ e)),
      ((children p t (primePowerProjection p (Nat.le_of_lt ht) c)).erase
        (primePowerProjection p (Nat.succ_le_of_lt ht) c)).card = p - 1 ∧
      (siblings p e t ht ((children p t (primePowerProjection p (Nat.le_of_lt ht) c)).erase
        (primePowerProjection p (Nat.succ_le_of_lt ht) c))).Nonempty) ∧
    (∀ (S : Finset (ZMod (p ^ e))) (c : ZMod (p ^ e)),
      (∀ r s, r ≠ s → Disjoint (S.filter (fun a => residueReadout p e c a = r))
        (S.filter (fun a => residueReadout p e c a = s))) ∧
      ((Finset.range (e + 1)).biUnion
        (fun r => S.filter (fun a => residueReadout p e c a = r)) = S)) ∧
    (∀ (d : ℕ) (hd : d < e) (I : Finset (ZMod (p ^ (d + 1)))),
      (∀ j ∈ I, (node p e (d + 1) (Nat.succ_le_of_lt hd) j).card = p ^ (e - (d + 1))) ∧
      ((d + 1=e ∧ ∀ j ∈ I, (node p e (d + 1) (Nat.succ_le_of_lt hd) j).card = 1) ∨
       (d + 1<e ∧ ∀ j ∈ I, 1 < (node p e (d + 1) (Nat.succ_le_of_lt hd) j).card))) ∧
    ((e = 0 → (Finset.univ : Finset (ZMod (p ^ e))) = {0}) ∧
      (∀ h : 0 < e, (Finset.univ : Finset (ZMod (p ^ e))) = siblings p e 0 h (children p 0 0)) ∧
      (∀ b : ZMod (p ^ 0), node p e 0 (Nat.zero_le e) b = Finset.univ)) ∧
    (∀ (b c : ZMod (p ^ e)) (r : ℕ),
      (({b} : Finset (ZMod (p ^ e))).filter (fun a => residueReadout p e c a = r)).Nonempty →
      ({b} : Finset (ZMod (p ^ e))).filter (fun a => residueReadout p e c a = r) = {b}) ∧
    (∀ H : List (ZMod (p ^ e) × ℕ),
      (candidates p e H).Nonempty → stateShape p e (candidates p e H)) ∧
    (∀ D : List (ZMod (p ^ e) × ℕ) → Option (ZMod (p ^ e)),
      (∀ (H P : List (ZMod (p ^ e) × ℕ)) (a : ZMod (p ^ e)),
        (runPassiveProtocol (residueReadout p e) (unroll D H.length P) a).map
          (fun z => (z.1,z.2)) = H ↔
          legal D P H ∧ ∀ z ∈ H, residueReadout p e z.1 a = z.2) ∧
      (∀ (n m : ℕ), n ≤ m → ∀ (P : List (ZMod (p ^ e) × ℕ)) (a : ZMod (p ^ e)),
        (runPassiveProtocol (residueReadout p e) (unroll D m P) a).take n =
          runPassiveProtocol (residueReadout p e) (unroll D n P) a) ∧
      (∀ H, legal D [] H → actualEvent p e D H = candidates p e H) ∧
      (∀ H c r, legal D [] H → D H = some c →
        actualEvent p e D (H ++ [(c,r)]) =
          (candidates p e H).filter (fun a => residueReadout p e c a = r))) ∧
    (∀ S : Finset (ZMod (p ^ e)), S.Nonempty → 0 < ∑ a ∈ S, μ a) ∧
    (e = 0 → ∀ a, μ a = 1) ∧
    (∃ hn : ∑ a, ENNReal.ofReal (μ a : ℝ) = 1,
      let prior := PMF.ofFintype (fun a => ENNReal.ofReal (μ a : ℝ)) hn
      prior.support = Set.univ ∧
      ∀ (D : List (ZMod (p ^ e) × ℕ) → Option (ZMod (p ^ e))) (H : List (ZMod (p ^ e) × ℕ)),
      0 < ∑ a ∈ actualEvent p e D H, μ a →
      ∃ hs : ∃ a ∈ (actualEvent p e D H : Set (ZMod (p ^ e))), a ∈ prior.support,
        legal D [] H ∧ actualEvent p e D H = candidates p e H ∧
        (candidates p e H).Nonempty ∧ stateShape p e (candidates p e H) ∧
        (prior.filter (actualEvent p e D H) hs).support = (candidates p e H : Set (ZMod (p ^ e))) ∧
        (∀ a, (prior.filter (actualEvent p e D H) hs) a =
          if a ∈ candidates p e H then
            ENNReal.ofReal ((μ a / ∑ b ∈ candidates p e H, μ b : ℚ) : ℝ) else 0) ∧
        (∀ (c : ZMod (p ^ e)) (r : ℕ),
          let F := (candidates p e H).filter (fun a => residueReadout p e c a = r)
          let R := (Finset.univ : Finset (ZMod (p ^ e))).filter
            (fun a => residueReadout p e c a = r)
          F.Nonempty →
          0 < ∑ a ∈ F, μ a ∧
          (∑ a ∈ R, (prior.filter (actualEvent p e D H) hs) a) =
            ENNReal.ofReal (((∑ a ∈ F, μ a) / ∑ b ∈ candidates p e H, μ b : ℚ) : ℝ) ∧
          0 < ∑ a ∈ R, (prior.filter (actualEvent p e D H) hs) a ∧
          ∃ (hF : ∃ a ∈ (F : Set (ZMod (p ^ e))), a ∈ prior.support)
            (hR : ∃ a ∈ (R : Set (ZMod (p ^ e))),
              a ∈ (prior.filter (actualEvent p e D H) hs).support),
            (prior.filter (actualEvent p e D H) hs).filter R hR = prior.filter F hF ∧
            ∀ a, (prior.filter F hF) a =
              if a ∈ F then ENNReal.ofReal ((μ a / ∑ b ∈ F, μ b : ℚ) : ℝ) else 0)) := by
  have hp : p.Prime := Fact.out
  classical
  have proj (E k : ℕ) (hk : k ≤ E) (a c : ZMod (p ^ E)) :
      primePowerProjection p hk a = primePowerProjection p hk c ↔
        Nat.ModEq (p ^ k) a.val c.val := by
    simp only [primePowerProjection, ZMod.castHom_apply, ZMod.cast_eq_val,
      ZMod.natCast_eq_natCast_iff]
  have bound (a c : ZMod (p ^ e)) : residueReadout p e c a ≤ e := by
    by_cases he : e = 0
    · subst e
      simp [residueReadout]
    · simpa only [PrimePowerNonadaptiveResolution.depth, residueReadout,
        ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff'] using
        ((PrimePowerNonadaptiveResolution.result p e (by omega)).1 c a).1
  have threshold (k : ℕ) (hk : k ≤ e) (a c : ZMod (p ^ e)) :
      k ≤ residueReadout p e c a ↔ primePowerProjection p hk a = primePowerProjection p hk c := by
    by_cases he : e = 0
    · subst e
      have hk0 : k = 0 := by omega
      subst k
      have : Subsingleton (ZMod (p ^ 0)) := by
        simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Nat.zero_le _⟩
    · simpa only [PrimePowerNonadaptiveResolution.depth, residueReadout,
        primePowerProjection, ZMod.castHom_apply, ZMod.cast_eq_val,
        ZMod.natCast_eq_natCast_iff'] using
        ((PrimePowerNonadaptiveResolution.result p e (by omega)).1 c a).2 k hk
  have cards (E k : ℕ) (hk : k ≤ E) (b : ZMod (p ^ k)) :
      (node p E k hk b).card = p ^ (E - k) := by
    let f := primePowerProjection p hk
    have onto : Function.Surjective f := ZMod.castHom_surjective (pow_dvd_pow p hk)
    have equal (c : ZMod (p ^ k)) :
        (node p E k hk c).card = (node p E k hk b).card :=
      AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (onto c) (onto b)
    have total := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod (p ^ E))))
      (t := (Finset.univ : Finset (ZMod (p ^ k)))) (f := f) (by simp)
    change Fintype.card (ZMod (p ^ E)) = ∑ c : ZMod (p ^ k), (node p E k hk c).card at total
    simp only [equal, Finset.sum_const, Finset.card_univ, smul_eq_mul, ZMod.card] at total
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k)
    calc
      p ^ k * (node p E k hk b).card = p ^ E := total.symm
      _ = p ^ k * p ^ (E - k) := by rw [← pow_add, Nat.add_sub_of_le hk]
  have down (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ e) (a b : ZMod (p ^ e))
      (h : primePowerProjection p hk a = primePowerProjection p hk b) :
      primePowerProjection p (hjk.trans hk) a = primePowerProjection p (hjk.trans hk) b :=
    (proj e j _ a b).2 (((proj e k _ a b).1 h).of_dvd (pow_dvd_pow p hjk))
  have comp (j k E : ℕ) (hj : j ≤ k) (hk : k ≤ E) (a : ZMod (p ^ E)) :
      primePowerProjection p hj (primePowerProjection p hk a) =
        primePowerProjection p (hj.trans hk) a :=
    congrArg (fun f : ZMod (p ^ E) →+* ZMod (p ^ j) => f a)
      ((vertical_prime_inverse_system p).2.1 j k E hj hk)
  have top (a c : ZMod (p ^ e)) : residueReadout p e c a = e ↔ a = c := by
    by_cases he : e = 0
    · subst e
      have : Subsingleton (ZMod (p ^ 0)) := by
        simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by simp [residueReadout]⟩
    · simpa only [PrimePowerNonadaptiveResolution.depth, residueReadout,
        ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff'] using
        (PrimePowerNonadaptiveResolution.result p e (by omega)).2.1 c a
  have exactDepth (t : ℕ) (ht : t < e) (a c : ZMod (p ^ e)) :
      residueReadout p e c a = t ↔
        primePowerProjection p (Nat.le_of_lt ht) a = primePowerProjection p (Nat.le_of_lt ht) c ∧
        primePowerProjection p (Nat.succ_le_of_lt ht) a ≠
          primePowerProjection p (Nat.succ_le_of_lt ht) c := by
    change _ ↔ _ ∧ ¬ _
    rw [← threshold t (Nat.le_of_lt ht) a c, ← threshold (t + 1) (Nat.succ_le_of_lt ht) a c]
    omega
  have siblingMem (d : ℕ) (hd : d < e) (I : Finset (ZMod (p ^ (d + 1)))) (a : ZMod (p ^ e)) :
      a ∈ siblings p e d hd I ↔ primePowerProjection p (Nat.succ_le_of_lt hd) a ∈ I := by
    simp only [siblings, Finset.mem_filter, Finset.mem_univ, true_and]
  have nodeMem (E d : ℕ) (hd : d ≤ E) (b : ZMod (p ^ d)) (a : ZMod (p ^ E)) :
      a ∈ node p E d hd b ↔ primePowerProjection p hd a = b := by
    simp only [node, Finset.mem_filter, Finset.mem_univ, true_and]
  have childMem (d : ℕ) (hd : d < e) (b : ZMod (p ^ d)) (a : ZMod (p ^ e)) :
      primePowerProjection p (Nat.succ_le_of_lt hd) a ∈ children p d b ↔
        primePowerProjection p (Nat.le_of_lt hd) a = b := by
    rw [children, nodeMem, comp]
  have siblingsNonempty (d : ℕ) (hd : d < e) (I : Finset (ZMod (p ^ (d + 1)))) :
      (siblings p e d hd I).Nonempty ↔ I.Nonempty := by
    constructor
    · rintro ⟨a, ha⟩; exact ⟨_, (siblingMem d hd I a).1 ha⟩
    · rintro ⟨j, hj⟩
      obtain ⟨a, ha⟩ := ZMod.castHom_surjective (pow_dvd_pow p (Nat.succ_le_of_lt hd)) j
      refine ⟨a, (siblingMem d hd I a).2 ?_⟩
      change primePowerProjection p (Nat.succ_le_of_lt hd) a = j at ha
      rwa [ha]
  have childCard (d : ℕ) (b : ZMod (p ^ d)) : (children p d b).card = p := by
    simpa only [children, Nat.add_sub_cancel_left, pow_one] using cards (d + 1) d (Nat.le_succ d) b
  have nonpathMem (t : ℕ) (ht : t < e) (a c : ZMod (p ^ e)) :
      a ∈ siblings p e t ht ((children p t (primePowerProjection p (Nat.le_of_lt ht) c)).erase
        (primePowerProjection p (Nat.succ_le_of_lt ht) c)) ↔ residueReadout p e c a = t := by
    rw [siblingMem, Finset.mem_erase, childMem t ht, exactDepth t ht]
    exact and_comm
  have nonpathCard (t : ℕ) (ht : t < e) (c : ZMod (p ^ e)) :
      ((children p t (primePowerProjection p (Nat.le_of_lt ht) c)).erase
        (primePowerProjection p (Nat.succ_le_of_lt ht) c)).card = p - 1 := by
    rw [Finset.card_erase_of_mem ((childMem t ht _ c).2 rfl), childCard]
  have nonpathNonempty (t : ℕ) (ht : t < e) (c : ZMod (p ^ e)) :
      (siblings p e t ht ((children p t (primePowerProjection p (Nat.le_of_lt ht) c)).erase
        (primePowerProjection p (Nat.succ_le_of_lt ht) c))).Nonempty := by
    rw [siblingsNonempty, ← Finset.card_pos, nonpathCard t ht]
    have := hp.two_le
    omega
  have geometry (d : ℕ) (hd : d < e) (b : ZMod (p ^ d))
      (I : Finset (ZMod (p ^ (d + 1)))) (valid : I ⊆ children p d b) (c : ZMod (p ^ e)) :
      (∀ a ∈ siblings p e d hd I, a ∈ node p e d (Nat.le_of_lt hd) b) ∧
      (c ∈ node p e d (Nat.le_of_lt hd) b → c ∉ siblings p e d hd I →
        ∀ a ∈ siblings p e d hd I, residueReadout p e c a = d) ∧
      (c ∉ node p e d (Nat.le_of_lt hd) b → ∀ b0 ∈ node p e d (Nat.le_of_lt hd) b,
        residueReadout p e c b0 < d ∧ ∀ a ∈ node p e d (Nat.le_of_lt hd) b,
          residueReadout p e c a = residueReadout p e c b0) ∧
      (c ∈ siblings p e d hd I →
        ((siblings p e d hd I).filter (fun a => residueReadout p e c a = d) =
          siblings p e d hd (I.erase (primePowerProjection p (Nat.succ_le_of_lt hd) c))) ∧
        (∀ t (_hdt : d < t) (hte : t < e),
          (siblings p e d hd I).filter (fun a => residueReadout p e c a = t) =
            siblings p e t hte ((children p t (primePowerProjection p (Nat.le_of_lt hte) c)).erase
              (primePowerProjection p (Nat.succ_le_of_lt hte) c))) ∧
        ((siblings p e d hd I).filter (fun a => residueReadout p e c a = e) = {c}) ∧
        (∀ r, r < d ∨ e < r →
          (siblings p e d hd I).filter (fun a => residueReadout p e c a = r) = ∅) ∧
        (((siblings p e d hd I).filter (fun a => residueReadout p e c a = d)).Nonempty ↔
          (I.erase (primePowerProjection p (Nat.succ_le_of_lt hd) c)).Nonempty)) := by
    have inside (a : ZMod (p ^ e)) (ha : a ∈ siblings p e d hd I) :
        a ∈ node p e d (Nat.le_of_lt hd) b :=
      (nodeMem e d _ b a).2 ((childMem d hd b a).1 (valid ((siblingMem d hd I a).1 ha)))
    have baseEq (a z : ZMod (p ^ e)) (ha : a ∈ node p e d (Nat.le_of_lt hd) b)
        (hz : z ∈ node p e d (Nat.le_of_lt hd) b) :
        primePowerProjection p (Nat.le_of_lt hd) a = primePowerProjection p (Nat.le_of_lt hd) z :=
      ((nodeMem e d _ b a).1 ha).trans ((nodeMem e d _ b z).1 hz).symm
    refine ⟨inside, ?_, ?_, ?_⟩
    · intro hc hnot a ha
      apply (exactDepth d hd a c).2
      refine ⟨baseEq a c (inside a ha) hc, ?_⟩
      intro heq
      apply hnot
      rw [siblingMem] at ha ⊢
      rwa [← heq]
    · intro hc b0 hb0
      have low : residueReadout p e c b0 < d := by
        by_contra h
        have eq := (threshold d (Nat.le_of_lt hd) b0 c).1 (by omega)
        exact hc ((nodeMem e d _ b c).2 (eq.symm.trans ((nodeMem e d _ b b0).1 hb0)))
      refine ⟨low, ?_⟩
      intro a ha
      have hte : residueReadout p e c b0 < e := low.trans hd
      obtain ⟨heq, hne⟩ := (exactDepth _ hte b0 c).1 rfl
      apply (exactDepth _ hte a c).2
      constructor
      · exact (down _ d (Nat.le_of_lt low) (Nat.le_of_lt hd) a b0 (baseEq a b0 ha hb0)).trans heq
      · intro he
        apply hne
        exact (down _ d (Nat.succ_le_of_lt low) (Nat.le_of_lt hd) a b0
          (baseEq a b0 ha hb0)).symm.trans he
    · intro hc
      have pc := inside c hc
      have parentFiber : (siblings p e d hd I).filter (fun a => residueReadout p e c a = d) =
          siblings p e d hd (I.erase (primePowerProjection p (Nat.succ_le_of_lt hd) c)) := by
        ext a
        rw [Finset.mem_filter, siblingMem d hd (I.erase _) a, Finset.mem_erase,
          ← siblingMem d hd I a]
        constructor
        · rintro ⟨ha, hr⟩
          exact ⟨((exactDepth d hd a c).1 hr).2, ha⟩
        · rintro ⟨hne, ha⟩
          exact ⟨ha, (exactDepth d hd a c).2 ⟨baseEq a c (inside a ha) pc, hne⟩⟩
      refine ⟨parentFiber, ?_, ?_, ?_, ?_⟩
      · intro t hdt hte
        ext a
        rw [Finset.mem_filter, nonpathMem]
        constructor
        · exact And.right
        · intro h
          refine ⟨?_, h⟩
          have he := down (d + 1) t (by omega) (Nat.le_of_lt hte) a c
            ((exactDepth t hte a c).1 h).1
          rw [siblingMem, he]
          exact (siblingMem d hd I c).1 hc
      · ext a
        simp only [Finset.mem_filter, top, Finset.mem_singleton]
        exact ⟨And.right, fun h => ⟨h ▸ hc, h⟩⟩
      · intro r hr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
        have hl := (threshold d (Nat.le_of_lt hd) a c).2 (baseEq a c (inside a ha) pc)
        have hu := bound a c
        omega
      · rw [parentFiber, siblingsNonempty]
  have outsideConstant (d : ℕ) (hd : d < e) (b : ZMod (p ^ d))
      (I : Finset (ZMod (p ^ (d + 1)))) (ne : I.Nonempty) (valid : I ⊆ children p d b)
      (c : ZMod (p ^ e)) (hc : c ∉ siblings p e d hd I) :
      ∃ r ≤ e, ∀ a ∈ siblings p e d hd I, residueReadout p e c a = r := by
    obtain ⟨a0, ha0⟩ := (siblingsNonempty d hd I).2 ne
    have g := geometry d hd b I valid c
    by_cases hb : c ∈ node p e d (Nat.le_of_lt hd) b
    · exact ⟨d, Nat.le_of_lt hd, g.2.1 hb hc⟩
    · exact ⟨residueReadout p e c a0, bound a0 c,
        fun a ha => (g.2.2.1 hb a0 (g.1 a0 ha0)).2 a (g.1 a ha)⟩
  have rootZero (h : e = 0) : (Finset.univ : Finset (ZMod (p ^ e))) = {0} := by
    subst e
    ext a
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    have : Subsingleton (ZMod (p ^ 0)) := by
      simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  have rootPositive (h : 0 < e) :
      (Finset.univ : Finset (ZMod (p ^ e))) = siblings p e 0 h (children p 0 0) := by
    ext a
    rw [siblingMem, childMem 0 h]
    simp only [Finset.mem_univ, true_iff]
    have : Subsingleton (ZMod (p ^ 0)) := by
      simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  have rootNode (b : ZMod (p ^ 0)) : node p e 0 (Nat.zero_le e) b = Finset.univ := by
    ext a
    rw [nodeMem]
    simp only [Finset.mem_univ, iff_true]
    have : Subsingleton (ZMod (p ^ 0)) := by
      simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  have rootShape : stateShape p e Finset.univ := by
    by_cases h : e = 0
    · exact Or.inl ⟨0, rootZero h⟩
    · have he : 0 < e := Nat.pos_of_ne_zero h
      refine Or.inr ⟨0, he, 0, children p 0 0, ?_, Finset.Subset.refl _, rootPositive he⟩
      rw [← Finset.card_pos, childCard]
      exact hp.pos
  have updateShape (S : Finset (ZMod (p ^ e))) (hs : stateShape p e S) (c : ZMod (p ^ e))
      (r : ℕ) (hn : (S.filter (fun a => residueReadout p e c a = r)).Nonempty) :
      stateShape p e (S.filter (fun a => residueReadout p e c a = r)) := by
    let a0 := hn.choose
    have ha0 : a0 ∈ S.filter (fun a => residueReadout p e c a = r) := hn.choose_spec
    obtain ⟨ha0, hr0⟩ := Finset.mem_filter.mp ha0
    rcases hs with ⟨a, rfl⟩ | ⟨d, hd, b, I, ne, valid, rfl⟩
    · have ha : a0 = a := Finset.mem_singleton.mp ha0
      have hr : residueReadout p e c a = r := ha ▸ hr0
      exact Or.inl ⟨a, by simp [hr]⟩
    · by_cases hc : c ∈ siblings p e d hd I
      · have g := (geometry d hd b I valid c).2.2.2 hc
        by_cases rd : r = d
        · rw [rd, g.1] at hn ⊢
          exact Or.inr ⟨d, hd, b, _, (siblingsNonempty d hd _).1 hn,
            (Finset.erase_subset _ _).trans valid, rfl⟩
        · by_cases re : r = e
          · exact Or.inl ⟨c, by simpa only [re] using g.2.2.1⟩
          · have hrge : d ≤ r := by
              by_contra h
              have hempty := g.2.2.2.1 r (Or.inl (by omega))
              exact Finset.not_nonempty_empty (hempty ▸ hn)
            have hrle : r ≤ e := hr0 ▸ bound a0 c
            have hdr : d < r := by omega
            have hre : r < e := by omega
            rw [g.2.1 r hdr hre]
            exact Or.inr ⟨r, hre, primePowerProjection p (Nat.le_of_lt hre) c, _,
              (siblingsNonempty r hre _).1 (nonpathNonempty r hre c), Finset.erase_subset _ _, rfl⟩
      · obtain ⟨t, _, ht⟩ := outsideConstant d hd b I ne valid c hc
        have tr : t = r := (ht a0 ha0).symm.trans hr0
        have same : (siblings p e d hd I).filter (fun a => residueReadout p e c a = r) =
            siblings p e d hd I := by
          exact Finset.filter_eq_self.mpr (fun a ha => (ht a ha).trans tr)
        rw [same]
        exact Or.inr ⟨d, hd, b, I, ne, valid, rfl⟩
  have snocCandidates (H : List (ZMod (p ^ e) × ℕ)) (c : ZMod (p ^ e)) (r : ℕ) :
      candidates p e (H ++ [(c,r)]) =
        (candidates p e H).filter (fun a => residueReadout p e c a = r) := by
    ext a
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and,
      List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, forall_false, implies_true,
      and_true]
  have candidateShape (H : List (ZMod (p ^ e) × ℕ)) (hn : (candidates p e H).Nonempty) :
      stateShape p e (candidates p e H) := by
    induction H using List.reverseRecOn with
    | nil => simpa [candidates] using rootShape
    | append_singleton H z ih =>
      obtain ⟨c,r⟩ := z
      rw [snocCandidates] at hn ⊢
      apply updateShape _ (ih (hn.mono (Finset.filter_subset _ _))) c r hn
  have partition (S : Finset (ZMod (p ^ e))) (c : ZMod (p ^ e)) :
      (∀ r s, r ≠ s → Disjoint (S.filter (fun a => residueReadout p e c a = r))
        (S.filter (fun a => residueReadout p e c a = s))) ∧
      ((Finset.range (e + 1)).biUnion
        (fun r => S.filter (fun a => residueReadout p e c a = r)) = S) := by
    constructor
    · intro r s h
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact h ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
    · ext a
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun ⟨_, _, ha, _⟩ => ha,
        fun ha => ⟨_, Finset.mem_range.mpr (by have := bound a c; omega), ha, rfl⟩⟩
  have noMixing (d : ℕ) (hd : d < e) (I : Finset (ZMod (p ^ (d + 1)))) :
      (∀ j ∈ I, (node p e (d + 1) (Nat.succ_le_of_lt hd) j).card = p ^ (e - (d + 1))) ∧
      ((d + 1=e ∧ ∀ j ∈ I, (node p e (d + 1) (Nat.succ_le_of_lt hd) j).card = 1) ∨
       (d + 1<e ∧ ∀ j ∈ I, 1 < (node p e (d + 1) (Nat.succ_le_of_lt hd) j).card)) := by
    refine ⟨fun j _ => cards e (d + 1) _ j, ?_⟩
    by_cases he : d + 1=e
    · exact Or.inl ⟨he, fun j _ => by rw [cards, he, Nat.sub_self, pow_zero]⟩
    · refine Or.inr ⟨by omega, fun j _ => ?_⟩
      rw [cards]
      exact one_lt_pow₀ (by have := hp.two_le; omega) (by omega)
  have siblingUnion (d : ℕ) (hd : d < e) (I : Finset (ZMod (p ^ (d + 1)))) :
      siblings p e d hd I = I.biUnion (node p e (d + 1) (Nat.succ_le_of_lt hd)) := by
    ext a
    simp only [siblingMem, Finset.mem_biUnion, nodeMem]
    exact ⟨fun h => ⟨_,h,rfl⟩, fun ⟨j,hj,he⟩ => he.symm ▸ hj⟩
  have parentUnion (d : ℕ) (hd : d < e) (b : ZMod (p ^ d)) :
      (children p d b).biUnion (node p e (d + 1) (Nat.succ_le_of_lt hd)) =
        node p e d (Nat.le_of_lt hd) b := by
    rw [← siblingUnion d hd]
    ext a
    rw [siblingMem, childMem d hd, nodeMem]
  have nodeDisjoint (d : ℕ) (hd : d ≤ e) (b c : ZMod (p ^ d)) (hne : b ≠ c) :
      Disjoint (node p e d hd b) (node p e d hd c) := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    rw [nodeMem] at ha hc
    exact hne (ha.symm.trans hc)
  have singletonUpdate (b c : ZMod (p ^ e)) (r : ℕ)
      (hn : (({b} : Finset (ZMod (p ^ e))).filter (fun a => residueReadout p e c a = r)).Nonempty) :
      ({b} : Finset (ZMod (p ^ e))).filter (fun a => residueReadout p e c a = r) = {b} := by
    obtain ⟨a,ha⟩ := hn
    obtain ⟨ha,hr⟩ := Finset.mem_filter.mp ha
    have hab := Finset.mem_singleton.mp ha
    have hbr : residueReadout p e c b = r := hab ▸ hr
    simp [hbr]
  have eqn (D : List (ZMod (p ^ e) × ℕ) → Option (ZMod (p ^ e)))
      (H P : List (ZMod (p ^ e) × ℕ)) (a : ZMod (p ^ e)) :
      (runPassiveProtocol (residueReadout p e) (unroll D H.length P) a).map
          (fun z => (z.1,z.2)) = H ↔
        legal D P H ∧ ∀ z ∈ H, residueReadout p e z.1 a = z.2 := by
    induction H generalizing P with
    | nil => simp [unroll, runPassiveProtocol, legal]
    | cons z H ih =>
      obtain ⟨c,r⟩ := z
      cases h : D P with
      | none => simp [unroll, h, runPassiveProtocol, legal]
      | some x =>
        simp only [List.length_cons, unroll, h, runPassiveProtocol, List.map_cons,
          List.cons.injEq, Prod.mk.injEq, legal, Option.some.injEq, List.forall_mem_cons]
        constructor
        · rintro ⟨⟨rfl, rfl⟩, ht⟩
          exact ⟨⟨rfl, (ih _).1 ht |>.1⟩, rfl, (ih _).1 ht |>.2⟩
        · rintro ⟨⟨rfl, hl⟩, rfl, hr⟩
          exact ⟨⟨rfl, rfl⟩, (ih _).2 ⟨hl, hr⟩⟩
  have prefixRun (D : List (ZMod (p ^ e) × ℕ) → Option (ZMod (p ^ e)))
      (n m : ℕ) (h : n ≤ m) (P : List (ZMod (p ^ e) × ℕ)) (a : ZMod (p ^ e)) :
      (runPassiveProtocol (residueReadout p e) (unroll D m P) a).take n =
        runPassiveProtocol (residueReadout p e) (unroll D n P) a := by
    induction n generalizing m P with
    | zero => simp [unroll, runPassiveProtocol]
    | succ n ih =>
      cases m with
      | zero => omega
      | succ m =>
        cases hc : D P with
        | none => simp [unroll, hc, runPassiveProtocol]
        | some c =>
          simp only [unroll, hc, runPassiveProtocol, List.take_succ_cons]
          congr 1
          exact ih m (by omega) _
  have eventForLegal (D : List (ZMod (p ^ e) × ℕ) → Option (ZMod (p ^ e)))
      (H : List (ZMod (p ^ e) × ℕ)) (hc : legal D [] H) :
      actualEvent p e D H = candidates p e H := by
    ext a
    simp only [actualEvent, candidates, Finset.mem_filter, Finset.mem_univ, true_and, eqn]
    exact and_iff_right hc
  have eventSnoc (D : List (ZMod (p ^ e) × ℕ) → Option (ZMod (p ^ e)))
      (H : List (ZMod (p ^ e) × ℕ)) (c : ZMod (p ^ e)) (r : ℕ)
      (hl : legal D [] H) (hc : D H = some c) :
      actualEvent p e D (H ++ [(c,r)]) =
        (candidates p e H).filter (fun a => residueReadout p e c a = r) := by
    have ls (L P : List (ZMod (p ^ e) × ℕ)) :
        legal D P (L ++ [(c,r)]) ↔ legal D P L ∧ D (P ++ L) = some c := by
      induction L generalizing P with
      | nil => simp [legal]
      | cons z L ih =>
        obtain ⟨x,t⟩ := z
        simp only [List.cons_append, legal, ih, List.append_assoc]
        exact and_assoc.symm
    rw [eventForLegal D _ ((ls H []).2 ⟨hl, by simpa using hc⟩), snocCandidates]
  have massPos (S : Finset (ZMod (p ^ e))) (hne : S.Nonempty) : 0 < ∑ a ∈ S, μ a :=
    Finset.sum_pos (fun a _ => positive a) hne
  have castMass (S : Finset (ZMod (p ^ e))) :
      (∑ a ∈ S, ENNReal.ofReal (μ a : ℝ)) = ENNReal.ofReal ((∑ a ∈ S, μ a : ℚ) : ℝ) := by
    rw [Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg (fun a _ => by exact_mod_cast (positive a).le)]
  have hn : ∑ a, ENNReal.ofReal (μ a : ℝ) = 1 := by
    rw [castMass, normalized, Rat.cast_one, ENNReal.ofReal_one]
  let prior := PMF.ofFintype (fun a => ENNReal.ofReal (μ a : ℝ)) hn
  have support : prior.support = Set.univ := by
    ext a
    simp only [PMF.mem_support_iff, prior, PMF.ofFintype_apply, Set.mem_univ, iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by exact_mod_cast positive a))
  have supported (S : Finset (ZMod (p ^ e))) (hne : S.Nonempty) :
      ∃ a ∈ (S : Set (ZMod (p ^ e))), a ∈ prior.support := by
    obtain ⟨a,ha⟩ := hne
    exact ⟨a,ha,by rw [support]; trivial⟩
  have value (S : Finset (ZMod (p ^ e))) (hne : S.Nonempty)
      (hs : ∃ a ∈ (S : Set (ZMod (p ^ e))), a ∈ prior.support)
      (a : ZMod (p ^ e)) : (prior.filter S hs) a =
        if a ∈ S then ENNReal.ofReal ((μ a / ∑ b ∈ S, μ b : ℚ) : ℝ) else 0 := by
    have den : ∑' b, (S : Set (ZMod (p ^ e))).indicator prior b =
        ENNReal.ofReal ((∑ b ∈ S, μ b : ℚ) : ℝ) := by
      rw [tsum_fintype]
      simpa only [Set.indicator_apply, Finset.mem_coe, prior, PMF.ofFintype_apply,
        ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] using castMass S
    rw [PMF.filter_apply, den]
    by_cases ha : a ∈ S
    · rw [if_pos ha, Set.indicator_of_mem ha]
      change ENNReal.ofReal (μ a : ℝ) * _ = _
      have realPos : (0 : ℝ) < ((∑ b ∈ S, μ b : ℚ) : ℝ) := by
        exact_mod_cast massPos S hne
      rw [Rat.cast_div, ENNReal.ofReal_div_of_pos realPos, div_eq_mul_inv]
    · simp only [Set.indicator_of_notMem ha, zero_mul, if_neg ha]
  have sumValue (S T : Finset (ZMod (p ^ e))) (hne : S.Nonempty)
      (hs : ∃ a ∈ (S : Set (ZMod (p ^ e))), a ∈ prior.support) :
      ∑ a ∈ T, (prior.filter S hs) a =
        ENNReal.ofReal (((∑ a ∈ S ∩ T, μ a) / ∑ b ∈ S, μ b : ℚ) : ℝ) := by
    simp only [value S hne hs]
    rw [← Finset.sum_filter]
    have inter : T.filter (fun a => a ∈ S) = S ∩ T := by ext a; simp [and_comm]
    rw [inter, ← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← Rat.cast_sum, ← Finset.sum_div]
    · intro a ha
      exact_mod_cast (div_nonneg (positive a).le (massPos S hne).le)
  have sequential (S T : Finset (ZMod (p ^ e))) (hne : S.Nonempty) (hF : (S ∩ T).Nonempty)
      (hs : ∃ a ∈ (S : Set (ZMod (p ^ e))), a ∈ prior.support) :
      ∃ ht : ∃ a ∈ (T : Set (ZMod (p ^ e))), a ∈ (prior.filter S hs).support,
        (prior.filter S hs).filter T ht =
          prior.filter ((S ∩ T : Finset (ZMod (p ^ e))) : Set (ZMod (p ^ e)))
            (supported (S ∩ T) hF) := by
    have ht : ∃ a ∈ (T : Set (ZMod (p ^ e))), a ∈ (prior.filter S hs).support := by
      obtain ⟨a,ha⟩ := hF
      obtain ⟨haS,haT⟩ := Finset.mem_inter.mp ha
      refine ⟨a,haT, (PMF.mem_support_filter_iff hs).2 ⟨haS,?_⟩⟩
      rw [support]; trivial
    refine ⟨ht, ?_⟩
    ext a
    rw [PMF.filter_apply, value (S ∩ T) hF]
    have den : (∑' b, (T : Set (ZMod (p ^ e))).indicator (prior.filter S hs) b) =
        ENNReal.ofReal (((∑ a ∈ S ∩ T, μ a) / ∑ b ∈ S, μ b : ℚ) : ℝ) := by
      rw [tsum_fintype]
      simpa only [Set.indicator_apply, Finset.mem_coe, ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.univ_inter] using sumValue S T hne hs
    rw [den]
    by_cases haT : a ∈ T
    · rw [Set.indicator_of_mem haT, value S hne hs]
      by_cases haS : a ∈ S
      · rw [if_pos haS, if_pos (Finset.mem_inter.mpr ⟨haS,haT⟩)]
        have hratio : (0 : ℝ) < ((∑ b ∈ S ∩ T, μ b) / ∑ b ∈ S, μ b : ℚ) := by
          exact_mod_cast div_pos (massPos _ hF) (massPos _ hne)
        rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hratio, ← Rat.cast_div]
        congr 2
        field_simp [(massPos _ hne).ne', (massPos _ hF).ne']
      · simp [haS]
    · simp [haT]
  refine ⟨threshold, exactDepth, top, cards e, ?_, geometry, ?_,
    (fun t ht c => ⟨nonpathCard t ht c, nonpathNonempty t ht c⟩), partition, noMixing,
    ⟨rootZero, rootPositive, rootNode⟩, singletonUpdate, candidateShape,
    (fun D => ⟨eqn D, prefixRun D, eventForLegal D, eventSnoc D⟩), massPos, ?_, hn, ?_⟩
  · intro d hd b
    exact ⟨childCard d b, parentUnion d hd b, nodeDisjoint (d + 1) _, siblingUnion d hd⟩
  · intro d hd b I ne valid c hc
    obtain ⟨r,hre,hr⟩ := outsideConstant d hd b I ne valid c hc
    refine ⟨r,hre,?_⟩
    intro t
    by_cases ht : t = r
    · rw [if_pos ht]
      exact Finset.filter_eq_self.mpr (fun a ha => (hr a ha).trans ht.symm)
    · rw [if_neg ht]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
      exact ht (he.symm.trans (hr a ha))
  · intro he a
    have hu : (Finset.univ : Finset (ZMod (p ^ e))) = {a} := by
      subst e
      have : Subsingleton (ZMod (p ^ 0)) := by
        simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim _ _
    simpa only [hu, Finset.sum_singleton] using normalized
  · refine ⟨support, ?_⟩
    intro D H hmass
    have nonemptyEvent : (actualEvent p e D H).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hmass
      exact lt_irrefl _ hmass
    have ha := nonemptyEvent.choose_spec
    have compatible : legal D [] H := ((eqn D H [] _).1 (Finset.mem_filter.mp ha).2).1
    have eventEq := eventForLegal D H compatible
    have ne : (candidates p e H).Nonempty := eventEq ▸ nonemptyEvent
    let hs := supported (actualEvent p e D H) nonemptyEvent
    refine ⟨hs, compatible, eventEq, ne, candidateShape H ne, ?_, ?_, ?_⟩
    · rw [PMF.support_filter, support, Set.inter_univ, eventEq]
    · intro a
      simpa only [eventEq] using value (actualEvent p e D H) nonemptyEvent hs a
    · intro c r
      dsimp only
      intro hF
      let F := (candidates p e H).filter (fun a => residueReadout p e c a = r)
      let R := (Finset.univ : Finset (ZMod (p ^ e))).filter (fun a => residueReadout p e c a = r)
      have inter : actualEvent p e D H ∩ R = F := by
        rw [eventEq]
        ext a
        simp only [R, F, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      have response := sumValue (actualEvent p e D H) R nonemptyEvent hs
      rw [inter] at response
      have massEq : (∑ a ∈ actualEvent p e D H, μ a) = ∑ a ∈ candidates p e H, μ a :=
        congrArg (fun S : Finset (ZMod (p ^ e)) => ∑ a ∈ S, μ a) eventEq
      rw [massEq] at response
      have responsePos : 0 < ∑ a ∈ R, (prior.filter (actualEvent p e D H) hs) a := by
        rw [response, ENNReal.ofReal_pos]
        exact_mod_cast div_pos (massPos F hF) (massPos _ ne)
      refine ⟨massPos F hF, response, responsePos, supported F hF, ?_⟩
      obtain ⟨hR, seq⟩ := sequential (actualEvent p e D H) R nonemptyEvent (inter.symm ▸ hF) hs
      refine ⟨hR, ?_, value F hF _⟩
      simpa only [inter] using seq

#print axioms residue_posterior_closure

end D5.S3.Observer.Budget.ResiduePosteriorClosure
