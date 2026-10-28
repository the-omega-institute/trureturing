/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativePolynomialDescriptorObstruction
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativePolynomialDescriptorObstruction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Separated-atom finite families cannot exactly read all native alpha replies. -/

import D5.S0.Computability.PresburgerFiniteFamilies
import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import Mathlib.Data.Fintype.EquivFin

/-!
An obstruction conditional on separated-atom Growth derivations. Source charts
may be arbitrary maps covering all finite native trees. Descriptor realizations
cover all physical addresses, and exactness holds for every admitted source and
every realization. No definability or injectivity of those maps is assumed.
This result does not assert that an arbitrary Presburger formula has Growth.
-/

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeDepthPatterns (Pattern Frontier fill frontierAddress frontier_geometry)
open PresburgerPatternGrowth (Growth traces mem_traces)
open PresburgerFiniteFamilies (joint finite_family_polynomial_bound finite_exponential_domination)
open scoped BigOperators

universe u v w z

/-- A complete binary shape with one frontier position at every depth-d address. -/
def fullPattern : (d : Nat) → Pattern d
  | 0 => ()
  | d + 1 => .inr (fullPattern d, fullPattern d)

theorem full_frontier_card (d : Nat) :
    Fintype.card (Frontier (fullPattern d)) = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change Fintype.card (Frontier (fullPattern d) ⊕ Frontier (fullPattern d)) = _
      rw [Fintype.card_sum, ih, pow_succ]
      omega

/-- Finite dependent chart/type families with supplied separated-atom Growth
cannot cover all native sources and physical addresses with exact alpha replies.
Realizations are related to their actual queried addresses, not a chosen proxy. -/
theorem growth_obstruction {K : Type u} {T : Type v} [Finite K] [Finite T]
    {X : K → Type w} {Y : T → Type z}
    (admitted : (k : K) → X k → Prop)
    (Theta : (k : K) → X k → Source)
    (Real : (t : T) → Y t → Address → Prop)
    (f : (k : K) → (t : T) → X k → Y t → Bool)
    (C s : K → T → Nat)
    (growth : ∀ k t, Growth (f k t) (C k t) (s k t))
    (source_cover : ∀ P : Source, ∃ k x, admitted k x ∧ Theta k x = P)
    (address_cover : ∀ a : Address, ∃ t y, Real t y a)
    (exactness : ∀ k t x y a, admitted k x → Real t y a →
      (f k t x y = true ↔ readout a (Theta k x) = .alpha)) : False := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite T
  let Ctotal := (∑ k, ∏ t, C k t) + 1
  let stotal := ∑ k, ∑ t, s k t
  obtain ⟨n, hn⟩ := finite_exponential_domination Ctotal stotal
  let p := fullPattern n
  let e : Fin n ↪ Frontier p := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin, p, full_frontier_card] using
        (Nat.le_of_lt (Nat.lt_two_pow_self (n := n)))))
  let a (i : Fin n) := frontierAddress p (e i)
  have covers : ∀ i : Fin n, ∃ y : Sigma Y, Real y.1 y.2 (a i) := by
    intro i
    obtain ⟨t,y,hy⟩ := address_cover (a i)
    exact ⟨⟨t,y⟩,hy⟩
  choose sample hs using covers
  have all_patterns : traces (fun x (i : Fin n) => joint f x (sample i)) =
      Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro b
    let val : Frontier p → Source :=
      Function.extend e (fun i => FreeMagma.of (b i)) (fun _ => FreeMagma.of false)
    let P := fill p val
    have replies (i : Fin n) : readout (a i) P =
        if b i then .alpha else .beta := by
      have readAt := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (frontierAddress p (e i)) [] (fill p val)
      rw [List.append_nil, (frontier_geometry n p).2.1 val (e i)] at readAt
      have hv : val (e i) = FreeMagma.of (b i) := e.injective.extend_apply _ _ i
      rw [hv] at readAt
      cases hb : b i <;> simpa [a, P, hb, readout] using readAt
    obtain ⟨k,x,hx,hP⟩ := source_cover P
    apply (mem_traces _ _).mpr
    refine ⟨⟨k,x⟩, funext fun i => ?_⟩
    have hi := exactness k (sample i).1 x (sample i).2 (a i) hx (hs i)
    rw [hP, replies i] at hi
    change f k (sample i).1 x (sample i).2 = b i
    cases hb : b i <;> cases hf : f k (sample i).1 x (sample i).2 <;>
      simp_all
  have bound := (finite_family_polynomial_bound f C s growth).2 sample
  rw [all_patterns, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at bound
  exact (Nat.not_le_of_gt hn) bound

#print axioms full_frontier_card
#print axioms growth_obstruction

end D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction
