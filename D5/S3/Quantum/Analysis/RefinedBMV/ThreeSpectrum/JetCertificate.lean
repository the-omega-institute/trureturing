/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/JetCertificate
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar positivity from checked signs of the mixed derivatives. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetBounds
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetEvaluation
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetMask

/-! Integer bounds and mask interpretation for the uniform scalar certificate. -/

open scoped BigOperators
open Polynomial

noncomputable section

namespace RefinedBMV.DividedDifference.SparseExpansion

def difference (a b : Rate) : ℤ × ℤ :=
  (((a.1 : ℤ) + a.2) - ((b.1 : ℤ) + b.2), (a.2 : ℤ) - b.2)

private theorem shifted_sub (a b : Rate) :
    Rate.shifted a - Rate.shifted b =
      C (difference a b).1 + C (difference a b).2 * X := by
  simp only [Rate.shifted, difference, map_sub]
  ring

private theorem term_eq_chain (t : Term) (xs ys : List Rate) :
    C t.coefficient * (1 + X)^t.exponents.p *
      rateFactor t.rateX xs * rateFactor t.rateY ys =
      JetBounds.affineChainTerm t.coefficient t.exponents.p
        (xs.map (difference t.rateX) ++ ys.map (difference t.rateY)) := by
  simp only [JetBounds.affineChainTerm, List.map_append, List.prod_append,
    List.map_map, Function.comp_def, rateFactor, shifted_sub, mul_assoc]

private theorem sum_get {T S : Type*} [AddCommMonoid S] (xs : List T) (f : T → S) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  rw [← List.sum_ofFn, ← List.ofFn_getElem (xs := xs)]
  simp

theorem jet_bounds (ts : List Term) (xs ys : List Rate)
    (hdegree : ∀ t ∈ ts, t.exponents.p ≤ 8)
    (hlength : xs.length + ys.length ≤ 128)
    (hx : ∀ t ∈ ts, ∀ x ∈ xs, |(difference t.rateX x).1| + |(difference t.rateX x).2| ≤ 42)
    (hy : ∀ t ∈ ts, ∀ y ∈ ys, |(difference t.rateY y).1| + |(difference t.rateY y).2| ≤ 42) :
    (∀ j, |(jet ts xs ys).coeff j| ≤
      (ts.map fun t => |t.coefficient| * 2 ^ t.exponents.p).sum * 42^128) ∧
      (jet ts xs ys).natDegree ≤ 136 := by
  let f (t : Term) : ℤ[X] := C t.coefficient * (1 + X)^t.exponents.p *
    rateFactor t.rateX xs * rateFactor t.rateY ys
  let b (t : Term) : ℤ := |t.coefficient| * 2 ^ t.exponents.p * 42^128
  have ht (t : Term) (hm : t ∈ ts) :
      (∀ j, |(f t).coeff j| ≤ b t) ∧ (f t).natDegree ≤ 136 := by
    dsimp only [f]
    rw [term_eq_chain]
    have h := JetBounds.affineChainTerm_bounds t.coefficient 42 t.exponents.p 128
      (xs.map (difference t.rateX) ++ ys.map (difference t.rateY))
      (by decide) (by simpa using hlength) ?_
    · exact ⟨h.1, h.2.trans (by have := hdegree t hm; omega)⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨x, hx', rfl⟩ := List.mem_map.mp ha
        exact hx t hm x hx'
      · obtain ⟨y, hy', rfl⟩ := List.mem_map.mp ha
        exact hy t hm y hy'
  have h := JetBounds.sum_bounds (Finset.univ : Finset (Fin ts.length))
    (fun i => f (ts.get i)) (fun i => b (ts.get i)) 136
    (fun i _ => ht _ (List.get_mem ts i))
  rw [sum_get ts f, sum_get ts b] at h
  dsimp only [b] at h
  rw [List.sum_map_mul_right] at h
  exact h

/-- A checked integer mask gives the signs needed by the continuum argument. -/
theorem nonneg_of_masks (ts : List Term) (rootsX rootsY : List Rate)
    (heval : ∀ p x y u v : ℝ, evalTerms p x y u v ts = clearedQuartic p x y u v)
    (sx : ∀ t ∈ ts, t.rateX ∈ rootsX) (sy : ∀ t ∈ ts, t.rateY ∈ rootsY)
    (hxlen : rootsX.length ≤ 65) (hylen : rootsY.length ≤ 65)
    (hdeg : ∀ t ∈ ts, t.exponents.p ≤ 8)
    (hx : ∀ a ∈ rootsX, ∀ b ∈ rootsX, |(difference a b).1| + |(difference a b).2| ≤ 42)
    (hy : ∀ a ∈ rootsY, ∀ b ∈ rootsY, |(difference a b).1| + |(difference a b).2| ≤ 42)
    (hnorm : (ts.map fun t => |t.coefficient| * 2 ^ t.exponents.p).sum ≤ 181066048)
    (hmasks : ∀ k < rootsX.length, ∀ l < rootsY.length,
      let value := (jet ts (rootsX.take k) (rootsY.take l)).eval (2 ^ 720)
      let mask := DimThree.PackedCheck.polynomialMask 719 137
      (value + ↑mask).toNat &&& mask = mask)
    (p s u : ℝ) (hp : 1 ≤ p) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    0 ≤ clearedQuartic p (Real.exp (3*s)) (Real.exp (3*(s+u))) (Real.exp (p*s))
      (Real.exp (p*(s+u))) := by
  apply quartic_nonneg_of_jets ts heval rootsX rootsY sx sy _ p s u hp hs hu
  intro k hk l hl z hz
  have hlen : (rootsX.take k).length + (rootsY.take l).length ≤ 128 := by
    simp only [List.length_take, min_eq_left hk.le, min_eq_left hl.le]
    omega
  obtain ⟨hc, hd⟩ := jet_bounds ts (rootsX.take k) (rootsY.take l)
    hdeg hlen
    (fun t ht b hb => hx _ (sx t ht) b (List.mem_of_mem_take hb))
    (fun t ht b hb => hy _ (sy t ht) b (List.mem_of_mem_take hb))
  refine DimThree.PackedCheck.eval₂_nonneg_of_polynomial_mask
    (jet ts (rootsX.take k) (rootsY.take l))
    (n := 137) (w := 719) (by omega) ?_ (hmasks k hk l hl) z hz
  intro i
  have h := (hc i).trans (mul_le_mul_of_nonneg_right hnorm (by positivity))
  have hsmall : (181066048 : ℤ) * 42^128 < 2^719 := by decide +kernel
  have habs := h.trans_lt hsmall
  exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2⟩


def pairBounds (rs : List Rate) : Bool :=
  rs.all fun a => rs.all fun b => decide (|(difference a b).1| + |(difference a b).2| ≤ 42)

def staticCheck (ts : List Term) (rootsX rootsY : List Rate) : Bool :=
  decide (rootsX.length ≤ 65 ∧ rootsY.length ≤ 65) &&
    ts.all (fun t => decide (t.exponents.p ≤ 8 ∧ t.rateX ∈ rootsX ∧ t.rateY ∈ rootsY)) &&
    pairBounds rootsX && pairBounds rootsY &&
    decide ((ts.map fun t => |t.coefficient| * 2 ^ t.exponents.p).sum ≤ 181066048)

theorem nonneg_of_static_check (ts : List Term) (rootsX rootsY : List Rate)
    (heval : ∀ p x y u v : ℝ, evalTerms p x y u v ts = clearedQuartic p x y u v)
    (hstatic : staticCheck ts rootsX rootsY = true)
    (hmasks : ∀ k < rootsX.length, ∀ l < rootsY.length,
      let value := (jet ts (rootsX.take k) (rootsY.take l)).eval (2 ^ 720)
      let mask := DimThree.PackedCheck.polynomialMask 719 137
      (value + ↑mask).toNat &&& mask = mask)
    (p s u : ℝ) (hp : 1 ≤ p) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    0 ≤ clearedQuartic p (Real.exp (3*s)) (Real.exp (3*(s+u))) (Real.exp (p*s))
      (Real.exp (p*(s+u))) := by
  simp only [staticCheck, pairBounds, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hstatic
  obtain ⟨⟨⟨⟨⟨hxlen, hylen⟩, hdeg⟩, hx⟩, hy⟩, hnorm⟩ := hstatic
  exact nonneg_of_masks ts rootsX rootsY heval
    (fun t ht => (hdeg t ht).2.1) (fun t ht => (hdeg t ht).2.2)
    hxlen hylen (fun t ht => (hdeg t ht).1) hx hy hnorm hmasks p s u hp hs hu

end RefinedBMV.DividedDifference.SparseExpansion
