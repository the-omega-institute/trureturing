/- GID: D5/S3/Arith/Coding/CapacityBoxOneBitRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/CapacityBoxOneBitRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Capacity-box edge colours depend only on axis and layer, and different axes use different bits. -/

import Mathlib.InformationTheory.Hamming
import D5.S1.Ledger.BoundedTimeSlice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.CapacityBoxOneBitRigidity

open scoped symmDiff

private def flipSupport {B : Nat} (x y : Fin B → Bool) : Finset (Fin B) :=
  Finset.univ.filter fun j => x j ≠ y j

/-- The colour of a unit Boolean edge is its unique changed bit. -/
noncomputable def edgeColour {B : Nat} {x y : Fin B → Bool}
    (h : hammingDist x y = 1) : Fin B :=
  Classical.choose (Finset.card_eq_one.mp (show (flipSupport x y).card = 1 from h))

open D5.S1.Ledger.BoundedTimeSlice (TailBox)

variable {P : Type*} [Fintype P] {A : P → ℕ}

/-- A directed unit edge increases one coordinate by one and fixes all others. -/
def UnitEdge (p : P) (a b : TailBox A) : Prop :=
  (b p).val = (a p).val + 1 ∧ ∀ q, q ≠ p → b q = a q

/-- An injective Boolean code sending each unit edge to Hamming distance one. -/
structure OneBitEmbedding (A : P → ℕ) (n : ℕ) where
  toFun : TailBox A → (Fin n → Bool)
  injective : Function.Injective toFun
  map_unitEdge : ∀ (p : P) (a b : TailBox A), UnitEdge p a b →
    hammingDist (toFun a) (toFun b) = 1

/-- Increase a coordinate whose current value is strictly below its capacity. -/
noncomputable def raise (a : TailBox A) (p : P) (h : (a p).val < A p) : TailBox A := by
  classical
  exact Function.update a p ⟨(a p).val + 1, Nat.add_lt_add_right h 1⟩

/-- The colour of the edge increasing the indicated coordinate. -/
noncomputable def unitEdgeColour {n : ℕ} (φ : OneBitEmbedding A n)
    (a : TailBox A) (p : P) (h : (a p).val < A p) : Fin n := by
  classical
  exact edgeColour (φ.map_unitEdge p a (raise a p h) (by
    constructor
    · simp [raise]
    · intro q hq
      simp [raise, hq]))


/-- The colour of a coordinate edge depends only on its axis and starting layer. -/
theorem colour_depends_only_on_layer {n : ℕ} (φ : OneBitEmbedding A n)
    (a b : TailBox A) (p : P) (hp : (a p).val < A p) (hb : (b p).val < A p)
    (hab : (a p).val = (b p).val) :
    unitEdgeColour φ a p hp = unitEdgeColour φ b p hb := by
  classical
  have layer_step : ∀ (a : TailBox A) (p q : P) (hpq : p ≠ q)
      (hp : (a p).val < A p) (hq : (a q).val < A q),
      unitEdgeColour φ a p hp =
        unitEdgeColour φ (raise a q hq) p (by simpa [raise, hpq] using hp) := by
    intro a p q hpq hp hq
    have square_step {B : Nat}
        (a b c d : Fin B → Bool)
        (hab : hammingDist a b = 1) (hbd : hammingDist b d = 1)
        (hac : hammingDist a c = 1) (hcd : hammingDist c d = 1)
        (had : a ≠ d) (hbc : b ≠ c) :
        edgeColour hab = edgeColour hcd := by
      classical
      have flipSupport_xor (x y z : Fin B → Bool) :
          flipSupport x z = flipSupport x y ∆ flipSupport y z := by
        ext i
        simp only [flipSupport, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_symmDiff]
        by_cases hxy : x i = y i <;> by_cases hyz : y i = z i
        · simp [hxy, hyz]
        · simp [hxy, hyz]
        · simp [hxy, hyz]
        · cases hx : x i <;> cases hy : y i <;> cases hz : z i <;> simp_all
      let p := edgeColour hab
      let q := edgeColour hbd
      let r := edgeColour hac
      let s := edgeColour hcd
      have hs1 : flipSupport a b = {p} := Classical.choose_spec (Finset.card_eq_one.mp hab)
      have hs2 : flipSupport b d = {q} := Classical.choose_spec (Finset.card_eq_one.mp hbd)
      have hs3 : flipSupport a c = {r} := Classical.choose_spec (Finset.card_eq_one.mp hac)
      have hs4 : flipSupport c d = {s} := Classical.choose_spec (Finset.card_eq_one.mp hcd)
      have hxor : (({p} : Finset (Fin B)) ∆ {q}) = (({r} : Finset (Fin B)) ∆ {s}) := by
        calc
          ({p} : Finset (Fin B)) ∆ {q} = flipSupport a b ∆ flipSupport b d := by rw [hs1, hs2]
          _ = flipSupport a c ∆ flipSupport c d := by
            rw [← flipSupport_xor a b d, ← flipSupport_xor a c d]
          _ = ({r} : Finset (Fin B)) ∆ {s} := by rw [hs3, hs4]
      have hpq : p ≠ q := by
        intro heq
        have : a = d := by
          have hsd : flipSupport a d = ∅ := by
            rw [flipSupport_xor a b d, hs1, hs2, heq]
            simp
          funext t
          by_contra hne
          have ht : t ∈ flipSupport a d := by simp [flipSupport, hne]
          rw [hsd] at ht
          simpa using ht
        exact had this
      have hp : p ∈ ({p} : Finset (Fin B)) ∆ {q} := by
        rw [Finset.mem_symmDiff]
        exact Or.inl ⟨by simp, by simpa using hpq⟩
      rw [hxor] at hp
      have hcases : p = r ∨ p = s := by
        rcases Finset.mem_symmDiff.mp hp with h | h
        · exact Or.inl (Finset.mem_singleton.mp h.1)
        · exact Or.inr (Finset.mem_singleton.mp h.1)
      rcases hcases with hpr | hps
      · have hsup : flipSupport a b = flipSupport a c := by rw [hs1, hs3, hpr]
        have hbcEq : b = c := by
          funext t
          have hm : t ∈ flipSupport a b ↔ t ∈ flipSupport a c := by rw [hsup]
          simp only [flipSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          cases hx : a t <;> cases hy : b t <;> cases hz : c t <;> simp_all
        exact False.elim (hbc hbcEq)
      · simpa [p, s] using hps
    classical
    let b := raise a p hp
    let c := raise a q hq
    have hcp : (c p).val < A p := by simpa [c, raise, hpq] using hp
    let d := raise c p hcp
    have hedge (x : TailBox A) (r : P) (hr : (x r).val < A r) :
        UnitEdge r x (raise x r hr) := by
      constructor
      · simp [raise]
      · intro t ht
        simp [raise, ht]
    have hbd : UnitEdge q b d := by
      constructor
      · simp [b, c, d, raise, hpq, Ne.symm hpq]
      · intro t ht
        by_cases htp : t = p
        · subst t
          simp [b, c, d, raise, hpq]
        · simp [b, c, d, raise, ht, htp]
    apply square_step (φ.toFun a) (φ.toFun b)
      (φ.toFun c) (φ.toFun d) (φ.map_unitEdge _ _ _ (hedge a p hp))
      (φ.map_unitEdge _ _ _ hbd) (φ.map_unitEdge _ _ _ (hedge a q hq))
      (φ.map_unitEdge _ _ _ (hedge c p hcp))
    · intro h
      have he := congrArg (fun x : TailBox A => (x p).val) (φ.injective h)
      simp [d, c, raise, hpq] at he
    · intro h
      have he := congrArg (fun x : TailBox A => (x p).val) (φ.injective h)
      simp [b, c, raise, hpq] at he
  let base : TailBox A := Function.update (fun r => ⟨0, Nat.zero_lt_succ (A r)⟩) p (a p)
  have hbase : (base p).val < A p := by simpa [base] using hp
  have transport : ∀ m, ∀ (x : TailBox A), (∑ r, (x r).val) = m →
      x p = a p → ∀ hx : (x p).val < A p,
      unitEdgeColour φ x p hx = unitEdgeColour φ base p hbase := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hsum hxp hx
      by_cases hz : ∀ q, q ≠ p → (x q).val = 0
      · have hxb : x = base := by
          funext q
          by_cases hqp : q = p
          · subst q
            simpa [base] using hxp
          · apply Fin.ext
            simpa [base, hqp] using hz q hqp
        subst x
        rfl
      · push Not at hz
        obtain ⟨q, hqp, hq⟩ := hz
        let y : TailBox A := Function.update x q
          ⟨(x q).val - 1, by have := (x q).isLt; omega⟩
        have hyp : y p = a p := by simpa [y, Ne.symm hqp] using hxp
        have hycap : (y p).val < A p := by simpa [y, Ne.symm hqp] using hx
        have hyq : (y q).val < A q := by
          have := (x q).isLt
          simp only [y, Function.update_self]
          omega
        have hyraise : raise y q hyq = x := by
          funext r
          by_cases hrq : r = q
          · subst r
            apply Fin.ext
            simp only [raise, Function.update_self, y]
            omega
          · simp [raise, y, hrq]
        have hlt : (∑ r, (y r).val) < (∑ r, (x r).val) := by
          apply Finset.sum_lt_sum
          · intro r _
            by_cases hrq : r = q
            · subst r
              simp [y]
            · simp [y, hrq]
          · refine ⟨q, Finset.mem_univ q, ?_⟩
            simp only [y, Function.update_self]
            omega
        have hrec := ih (∑ r, (y r).val) (by omega) y rfl hyp hycap
        have hstep := layer_step y p q (Ne.symm hqp) hycap hyq
        have hxy : unitEdgeColour φ x p hx = unitEdgeColour φ y p hycap := by
          simpa only [hyraise] using hstep.symm
        exact hxy.trans hrec
  exact (transport _ a rfl rfl hp).trans
    (transport _ b rfl (Fin.ext hab.symm) hb).symm

/-- Edges on different capacity axes always change different bits. -/
theorem different_axes_distinct_colours {n : ℕ} (φ : OneBitEmbedding A n)
    (a b : TailBox A) (p q : P) (hpq : p ≠ q)
    (hp : (a p).val < A p) (hq : (b q).val < A q) :
    unitEdgeColour φ a p hp ≠ unitEdgeColour φ b q hq := by
  classical
  let x : TailBox A := Function.update a q (b q)
  have hxp : (x p).val < A p := by simpa [x, hpq] using hp
  have hxq : (x q).val < A q := by simpa [x] using hq
  have hpa := colour_depends_only_on_layer φ a x p hp hxp (by simp [x, hpq])
  have hqb := colour_depends_only_on_layer φ b x q hq hxq (by simp [x])
  intro heq
  have hcol : unitEdgeColour φ x p hxp = unitEdgeColour φ x q hxq :=
    hpa.symm.trans (heq.trans hqb)
  have support (r : P) (hr : (x r).val < A r) :
      flipSupport (φ.toFun x) (φ.toFun (raise x r hr)) = {unitEdgeColour φ x r hr} :=
    Classical.choose_spec (Finset.card_eq_one.mp (φ.map_unitEdge r x (raise x r hr)
      (by constructor <;> simp_all [UnitEdge, raise])))
  have hrev : flipSupport (φ.toFun (raise x p hxp)) (φ.toFun x) =
      {unitEdgeColour φ x p hxp} := by
    rw [← support p hxp]
    ext t
    simp [flipSupport, ne_comm]
  have hnext : flipSupport (φ.toFun x) (φ.toFun (raise x q hxq)) =
      {unitEdgeColour φ x p hxp} := by rw [support q hxq, hcol]
  have hd : φ.toFun (raise x p hxp) = φ.toFun (raise x q hxq) := by
    funext t
    have hm : t ∈ flipSupport (φ.toFun (raise x p hxp)) (φ.toFun x) ↔
        t ∈ flipSupport (φ.toFun x) (φ.toFun (raise x q hxq)) := by rw [hrev, hnext]
    simp only [flipSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    cases ha : φ.toFun (raise x p hxp) t <;> cases hb : φ.toFun x t <;>
      cases hc : φ.toFun (raise x q hxq) t <;> simp_all
  have hval := congrArg (fun y : TailBox A => (y p).val) (φ.injective hd)
  simp [raise, hpq] at hval


end D5.S3.Arith.Coding.CapacityBoxOneBitRigidity
