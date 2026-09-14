/- GID: D5/S3/Factorization/Combinatorics/MarkedPrimeWordSnapshotFiber
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MarkedPrimeWordSnapshotFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked prime words split uniquely into the prime words of successive divisor quotients. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.OfFn
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MarkedPrimeWordSnapshotFiber

/-- A prime word is an ordered list of prime labels whose actual product is the endpoint. -/
def PrimeWord (n : ℕ) :=
  {w : List ℕ // (∀ p ∈ w, Nat.Prime p) ∧ w.prod = n}

/-- A snapshot records the actual prefix products at strictly increasing marks,
including the empty prefix and the complete prime word. -/
def SnapshotFiber (n k : ℕ) (d : Fin (k + 1) → ℕ) :=
  {z : PrimeWord n × (Fin (k + 1) → ℕ) //
    z.2 0 = 0 ∧ z.2 (Fin.last k) = z.1.val.length ∧ StrictMono z.2 ∧
    ∀ i : Fin (k + 1), (z.1.val.take (z.2 i)).prod = d i}

/-- Every strict divisor snapshot splits uniquely into prime words for its successive
quotients, and every mark is the total prime multiplicity of its observed prefix. -/
theorem snapshot_fiber_equiv_and_forced_marks
    (n k : ℕ) (d : Fin (k + 1) → ℕ)
    (_hn : 1 < n) (_hk : 1 ≤ k) (hfirst : d 0 = 1) (hlast : d (Fin.last k) = n)
    (hchain : ∀ i : Fin k, d i.castSucc ∣ d i.succ ∧ d i.castSucc < d i.succ) :
    (Nonempty (SnapshotFiber n k d ≃ (∀ i : Fin k, PrimeWord (d i.succ / d i.castSucc)))) ∧
      ∀ z : SnapshotFiber n k d, ∀ i : Fin (k + 1),
        z.val.2 i = (d i).factorization.sum (fun _ a => a) := by
  classical
  have hdmono : StrictMono d := Fin.strictMono_iff_lt_succ.mpr fun i => (hchain i).2
  have hdpos (i : Fin (k + 1)) : 0 < d i := by
    have := hdmono.monotone (Fin.zero_le i)
    omega
  have hbound (z : SnapshotFiber n k d) (i : Fin (k + 1)) :
      z.val.2 i ≤ z.val.1.val.length := by
    rw [← z.property.2.1]
    exact z.property.2.2.1.monotone (Fin.le_last i)
  have hmarks (z : SnapshotFiber n k d) (i : Fin (k + 1)) :
      z.val.2 i = (d i).factorization.sum (fun _ a => a) := by
    have hp := Nat.primeFactorsList_unique (z.property.2.2.2 i)
      (fun p hp => z.val.1.property.1 p (List.mem_of_mem_take hp))
    have hl := hp.length_eq
    rw [Nat.factorization_eq_primeFactorsList_multiset]
    change z.val.2 i = ((d i).primeFactorsList : Multiset ℕ).toFinsupp.sum (fun _ => id)
    rw [Multiset.toFinsupp_sum_eq]
    simpa only [Multiset.coe_card, List.length_take,
      Nat.min_eq_left (hbound z i)] using hl
  let split : SnapshotFiber n k d → (∀ i : Fin k, PrimeWord (d i.succ / d i.castSucc)) :=
    fun z i => ⟨(z.val.1.val.take (z.val.2 i.succ)).drop (z.val.2 i.castSucc), by
      constructor
      · intro p hp
        exact z.val.1.property.1 p (List.mem_of_mem_take (List.mem_of_mem_drop hp))
      · have hle : z.val.2 i.castSucc ≤ z.val.2 i.succ :=
          z.property.2.2.1.monotone (Fin.castSucc_le_succ i)
        have he := List.prod_take_mul_prod_drop
          (z.val.1.val.take (z.val.2 i.succ)) (z.val.2 i.castSucc)
        rw [List.take_take, Nat.min_eq_left hle, z.property.2.2.2 i.castSucc,
          z.property.2.2.2 i.succ] at he
        apply Nat.eq_of_mul_eq_mul_left (hdpos i.castSucc)
        rw [Nat.mul_div_cancel' (hchain i).1]
        exact he⟩
  have hinj : Function.Injective split := by
    intro x y hxy
    have hm : x.val.2 = y.val.2 := funext fun i => (hmarks x i).trans (hmarks y i).symm
    have hpref : ∀ i : Fin (k + 1),
        x.val.1.val.take (x.val.2 i) = y.val.1.val.take (y.val.2 i) := by
      intro i
      induction i using Fin.induction with
      | zero => simp [x.property.1, y.property.1]
      | succ i ih =>
        have hs := congrArg Subtype.val (congrFun hxy i)
        change (x.val.1.val.take (x.val.2 i.succ)).drop (x.val.2 i.castSucc) =
          (y.val.1.val.take (y.val.2 i.succ)).drop (y.val.2 i.castSucc) at hs
        have hx := List.take_append_drop (x.val.2 i.castSucc)
          (x.val.1.val.take (x.val.2 i.succ))
        have hy := List.take_append_drop (y.val.2 i.castSucc)
          (y.val.1.val.take (y.val.2 i.succ))
        rw [List.take_take, Nat.min_eq_left
          (x.property.2.2.1.monotone (Fin.castSucc_le_succ i))] at hx
        rw [List.take_take, Nat.min_eq_left
          (y.property.2.2.1.monotone (Fin.castSucc_le_succ i))] at hy
        rw [← hx, ← hy, ih, hs]
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simpa only [x.property.2.1, y.property.2.1, List.take_length] using hpref (Fin.last k)
    · exact hm
  have hsurj : Function.Surjective split := by
    intro v
    let L : List (List ℕ) := List.ofFn fun i : Fin k => (v i).val
    have hlen : L.length = k := List.length_ofFn
    have hget (i : Fin k) : L[i.val]'(by simp [hlen]) = (v i).val := by
      simp [L]
    have hprime : ∀ p ∈ L.flatten, Nat.Prime p := by
      intro p hp
      obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      exact (v i).property.1 p hp
    let m : Fin (k + 1) → ℕ := fun i => ((L.map List.length).take i.val).sum
    have hmzero : m 0 = 0 := by simp [m]
    have hmlast : m (Fin.last k) = L.flatten.length := by
      simp [m, ← hlen, ← List.map_take, List.length_flatten]
    have hstep (i : Fin k) : m i.succ = m i.castSucc + (v i).val.length := by
      simp [m, L]
    have hnonempty (i : Fin k) : 0 < (v i).val.length := by
      apply List.length_pos_of_prod_ne_one
      rw [(v i).property.2]
      intro h
      have he := Nat.mul_div_cancel' (hchain i).1
      rw [h, Nat.mul_one] at he
      have := (hchain i).2
      omega
    have hmmono : StrictMono m := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      rw [hstep i]
      exact Nat.lt_add_of_pos_right (hnonempty i)
    have hpref : ∀ i : Fin (k + 1), (L.take i.val).flatten.prod = d i := by
      intro i
      induction i using Fin.induction with
      | zero => simpa using hfirst.symm
      | succ i ih =>
        change (L.take i.val).flatten.prod = d i.castSucc at ih
        have ht := List.take_concat_get' L i.val (by simp [hlen])
        change (L.take (i.val + 1)).flatten.prod = d i.succ
        rw [← ht, List.flatten_append, List.prod_append]
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
          hget i, ih, (v i).property.2]
        exact Nat.mul_div_cancel' (hchain i).1
    have hprod : L.flatten.prod = n := by
      simpa only [Fin.val_last, ← hlen, List.take_length, hlast] using hpref (Fin.last k)
    let z : SnapshotFiber n k d := ⟨(⟨L.flatten, hprime, hprod⟩, m),
      hmzero, hmlast, hmmono, fun i => by
        change (L.flatten.take ((L.map List.length).take i.val).sum).prod = d i
        rw [List.take_sum_flatten]
        exact hpref i⟩
    refine ⟨z, ?_⟩
    funext i
    apply Subtype.ext
    change (L.flatten.take ((L.map List.length).take (i.val + 1)).sum).drop
      ((L.map List.length).take i.val).sum = (v i).val
    rw [List.drop_take_succ_flatten_eq_getElem L i.val (by simp [hlen])]
    exact hget i
  exact ⟨⟨Equiv.ofBijective split ⟨hinj, hsurj⟩⟩, hmarks⟩

#print axioms snapshot_fiber_equiv_and_forced_marks
end D5.S3.Factorization.Combinatorics.MarkedPrimeWordSnapshotFiber
