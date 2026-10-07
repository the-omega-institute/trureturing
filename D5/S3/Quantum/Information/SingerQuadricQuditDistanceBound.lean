/- GID: D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SingerQuadricQuditDistanceBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Odd-prime Singer-quadric qudit codes in projective planes have distance at most p+1. -/

/-
proof_shape: result: content.
escape_witness: no_proper_invariant_subspace, projective_bijective and
  count_submodule in the same-delivery SingerTracePlane module, through its
  result and this module's translated-line and moment proof.
admission_basis: open-problem-resolution (#13799; Proved)
Direct frozen dependencies: none. SingerTracePlane is a same-delivery prerequisite
  whose first Freeze must precede this module's Freeze.
Information-escape registration is paused under CLAUDE.md section 3.9.
Private theorem classification: every private theorem is bind-only with a live
  consumer; none supplies this module's witness.
-/

import D5.S3.Geometry.FiniteGeometry.SingerTracePlane
import Mathlib.LinearAlgebra.Matrix.Circulant

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace D5.S3.Quantum.Information.SingerQuadricQuditDistanceBound

def tauH {p : ℕ} [Fact p.Prime] (α : GaloisField p 3) : Fin (p ^ 2 + p + 1) → ZMod p :=
  fun i => if Algebra.trace (ZMod p) (GaloisField p 3) (α ^ i.val) = 0 then 1 else 0

def tauQ {p : ℕ} [Fact p.Prime] (α : GaloisField p 3) : Fin (p ^ 2 + p + 1) → ZMod p :=
  fun i => if Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (2 * i.val)) = 0 then 1 else 0

def A {p : ℕ} [Fact p.Prime] (α : GaloisField p 3) : Matrix (Fin (p ^ 2 + p + 1)) (Fin (p ^ 2 + p + 1)) (ZMod p) :=
  Matrix.circulant (tauH α)
def MQ {p : ℕ} [Fact p.Prime] (α : GaloisField p 3) : Matrix (Fin (p ^ 2 + p + 1)) (Fin (p ^ 2 + p + 1)) (ZMod p) :=
  Matrix.circulant (tauQ α)
def B {p : ℕ} [Fact p.Prime] (α : GaloisField p 3) := MQ α * A α

def H {p : ℕ} [Fact p.Prime] (α : GaloisField p 3) : Matrix (Fin (p ^ 2 + p + 1)) (Fin (p ^ 2 + p + 1) ⊕ Fin (p ^ 2 + p + 1)) (ZMod p) :=
  fun i j => Sum.elim (A α i) (B α i) j

def symp {p : ℕ} (v w : ((Fin (p ^ 2 + p + 1) → ZMod p) × (Fin (p ^ 2 + p + 1) → ZMod p))) : ZMod p :=
  dotProduct v.1 w.2 - dotProduct v.2 w.1

def stabilizers {p : ℕ} [Fact p.Prime] (α : GaloisField p 3) : Set ((Fin (p ^ 2 + p + 1) → ZMod p) × (Fin (p ^ 2 + p + 1) → ZMod p)) :=
  {v | ∃ c, v = (Matrix.vecMul c (A α), Matrix.vecMul c (B α))}

def centralizer {p : ℕ} [Fact p.Prime] (α : GaloisField p 3) : Set ((Fin (p ^ 2 + p + 1) → ZMod p) × (Fin (p ^ 2 + p + 1) → ZMod p)) :=
  {v | ∀ w ∈ stabilizers α, symp v w = 0}

def wt {p : ℕ} (v : ((Fin (p ^ 2 + p + 1) → ZMod p) × (Fin (p ^ 2 + p + 1) → ZMod p))) : ℕ :=
  (Finset.univ.filter fun i => v.1 i ≠ 0 ∨ v.2 i ≠ 0).card

def claim : Prop := ∀ (p : ℕ) (hp : p.Prime), 2 < p →
  ∀ α : @GaloisField p ⟨hp⟩ 3, orderOf α = p ^ 3 - 1 →
    ∃ v : (Fin (p ^ 2 + p + 1) → ZMod p) × (Fin (p ^ 2 + p + 1) → ZMod p), v ∈ @centralizer p ⟨hp⟩ α ∧
      v ∉ @stabilizers p ⟨hp⟩ α ∧ wt v ≤ p + 1


namespace Linear
variable {G F : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G] [Field F]
private theorem separator_kernel (a q : G → F) :
    (Matrix.circulant a).mulVec q +
      (Matrix.circulant q * Matrix.circulant a).mulVec (-Pi.single 0 1) = 0 := by
  have hcol : (Matrix.circulant q).mulVec (Pi.single 0 1) = q := by
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Matrix.mulVec_neg, Matrix.circulant_mul_comm q a,
    ← Matrix.mulVec_mulVec, hcol]
  exact add_neg_cancel _

private theorem stabilizer_pairing_zero (a q : G → F) (v : (G → F) × (G → F)) (hv : v ∈ {v | ∃ c, v = (Matrix.vecMul c (Matrix.circulant a), Matrix.vecMul c (Matrix.circulant q * Matrix.circulant a))}) :
    dotProduct v.1 q + dotProduct v.2 (-Pi.single 0 1) = 0 := by
  obtain ⟨c, rfl⟩ := hv
  dsimp only
  rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
    ← dotProduct_add, separator_kernel, dotProduct_zero]

private theorem diagonal_central (a q s : G → F)
    (has : (Matrix.circulant a).mulVec s = 1)
    (hqs : (Matrix.circulant q).mulVec (1 : G → F) = 1) :
    (s,s) ∈ {v | ∀ w : (G → F) × (G → F), (∃ c, w = (Matrix.vecMul c (Matrix.circulant a), Matrix.vecMul c (Matrix.circulant q * Matrix.circulant a))) → dotProduct v.1 w.2 - dotProduct v.2 w.1 = 0} := by
  rintro w ⟨c, rfl⟩
  dsimp only
  rw [dotProduct_comm s, ← Matrix.dotProduct_mulVec,
    dotProduct_comm s, ← Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_mulVec, has, hqs, sub_self]

private theorem diagonal_separator (q s : G → F) :
    dotProduct s q + dotProduct s (-Pi.single 0 1) = dotProduct s q - s 0 := by
  simp [dotProduct_neg, dotProduct, Pi.single_apply, sub_eq_add_neg]

private theorem nonstabilizer_of_separator (a q s : G → F)
    (hne : dotProduct s q ≠ s 0) : (s,s) ∉ {v | ∃ c, v = (Matrix.vecMul c (Matrix.circulant a), Matrix.vecMul c (Matrix.circulant q * Matrix.circulant a))} := by
  intro h
  have hz := stabilizer_pairing_zero a q (s,s) h
  rw [diagonal_separator] at hz
  exact hne (sub_eq_zero.mp hz)

end Linear

namespace Difference
variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
private def autocorrelation (D : Finset G) (r : G) : ℕ :=
  (Finset.univ.filter fun i => i ∈ D ∧ i+r ∈ D).card

private theorem sum_ind (D : Finset G) : ∑ i, (Set.indicator (D: Set G) (1 : G → ℤ)) i = D.card := by
  simp [Set.indicator]

private theorem ind_mul (D : Finset G) (i j : G) : (Set.indicator (D: Set G) (1 : G → ℤ)) i * (Set.indicator (D: Set G) (1 : G → ℤ)) j =
    if i ∈ D ∧ j ∈ D then 1 else 0 := by
  by_cases hi : i ∈ D <;> by_cases hj : j ∈ D <;> simp [Set.indicator, hi, hj]

private theorem gram_entry (D : Finset G) (i j : G) :
    (Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ℤ))) * (Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ℤ)))).transpose) i j =
      autocorrelation D (i-j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.circulant_apply, ind_mul,
    autocorrelation, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Fintype.sum_equiv (Equiv.subLeft j) _ _
  intro x
  congr 1
  have he : (j-x)+(i-j) = i-x := by abel
  simp only [Equiv.subLeft_apply, he]
  exact propext and_comm

private theorem gram_of_difference (D : Finset G) (k : ℕ) (hk : D.card = k)
    (hd : ∀ r : G, r ≠ 0 → autocorrelation D r = 1) :
    Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ℤ))) * (Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ℤ)))).transpose =
      ((k : ℤ)-1) • (1 : Matrix G G ℤ) + Matrix.of (fun _ _ => (1 : ℤ)) := by
  ext i j
  rw [gram_entry]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  by_cases hij : i=j
  · subst j
    simp [autocorrelation, hk]
  · simp [hd (i-j) (sub_ne_zero.mpr hij), hij]

private theorem gram_reverse (a : G → ℤ) :
    (Matrix.circulant a).transpose * Matrix.circulant a =
      Matrix.circulant a * (Matrix.circulant a).transpose := by
  rw [Matrix.transpose_circulant]
  exact Matrix.circulant_mul_comm _ _

private theorem first_moment (D Q : Finset G) :
    ∑ t, ((Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ℤ)))).mulVec ((Set.indicator (Q: Set G) (1 : G → ℤ)))) t = (D.card : ℤ)*Q.card := by
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hs (j : G) : ∑ t, (Set.indicator (D: Set G) (1 : G → ℤ)) (t-j) = D.card := by
    rw [← sum_ind D]
    exact Fintype.sum_equiv (Equiv.subRight j) _ _ (by intro t; rfl)
  simp_rw [hs]
  rw [← Finset.mul_sum, sum_ind]

end Difference

namespace Moments
variable {G : Type*} [Fintype G]

private theorem second_moment_of_gram [Sub G] [DecidableEq G] (a q : G → ℤ) (c k : ℤ)
    (hq : ∀ i, q i * q i = q i) (hs : ∑ i, q i = k)
    (hgram : (Matrix.circulant a).transpose * Matrix.circulant a =
      c • (1 : Matrix G G ℤ) + Matrix.of (fun (_ : G) (_ : G) => (1 : ℤ))) :
    ∑ t, ((Matrix.circulant a).mulVec q t)^2 = c*k+k^2 := by
  let C := Matrix.circulant a
  have hqq : dotProduct q q = k := by
    simp_rw [dotProduct, hq]
    exact hs
  change (∑ t, C.mulVec q t ^ 2) = _
  simp only [pow_two]
  change dotProduct (C.mulVec q) (C.mulVec q) = _
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, hgram]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    add_dotProduct, smul_dotProduct, hqq]
  have hone : (Matrix.of (fun (_ : G) (_ : G) => (1 : ℤ))).mulVec q = fun _ => k := by
    ext i
    simp [Matrix.mulVec, dotProduct, hs]
  rw [hone]
  simp only [dotProduct, ← Finset.mul_sum, hs]
  ring

private theorem residue_square_inequality (p m δ : ℕ) (hp : 2 < p)
    (hδ : δ ≤ 1) (hm : m ≤ p + 1) (hres : m % p = δ) :
    (p : ℤ) * ((m : ℤ) - δ) + δ ≤ (m : ℤ)^2 := by
  have hδp : δ < p := by omega
  let j := m / p
  have he : m = δ + p * j := by
    simpa [hres] using (Nat.mod_add_div m p).symm
  have hquot : j ≤ 1 := by
    by_contra! h
    have hd : p * j ≤ m := Nat.mul_div_le m p
    nlinarith
  have hd : δ = 0 ∨ δ = 1 := by omega
  have hh : j = 0 ∨ j = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hquot
  rcases hd with rfl | rfl <;> rcases hh with h | h
  all_goals rw [h] at he
  all_goals simp only [mul_zero, mul_one, add_zero, zero_add] at he
  all_goals rw [he]
  all_goals push_cast
  all_goals nlinarith

private theorem moments_force_nonzero_residue {p : ℕ} (hp : 2 < p)
    (m δ : G → ℕ)
    (hδ : ∀ i, δ i ≤ 1) (hm : ∀ i, m i ≤ p + 1)
    (hd : ∑ i, (δ i : ℤ) = (p : ℤ) + 1)
    (h1 : ∑ i, (m i : ℤ) = ((p : ℤ) + 1)^2)
    (h2 : ∑ i, (m i : ℤ)^2 = ((p : ℤ)+1)^2 + (p : ℤ)^2 + p) :
    ∃ i, m i % p ≠ δ i := by
  by_contra! hall
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    residue_square_inequality p (m i) (δ i) hp (hδ i) (hm i) (hall i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  rw [hd, h1, h2] at hsum
  have hp3 : 3 ≤ p := by omega
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hpos : (0 : ℤ) < p * ((p : ℤ) - 2) * ((p : ℤ) + 1) := by
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  nlinarith

end Moments

namespace Generic
open Difference
variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

private def mass (D Q : Finset G) (t : G) : ℕ :=
  (Finset.univ.filter fun j => t-j ∈ D ∧ j ∈ Q).card

private theorem mass_eq (D Q : Finset G) (t : G) :
    (mass D Q t : ℤ) = (Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ℤ)))).mulVec ((Set.indicator (Q: Set G) (1 : G → ℤ))) t := by
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, mass,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hd : t-j ∈ D <;> by_cases hq : j ∈ Q <;> simp [Set.indicator, hd, hq]

private theorem mass_le (D Q : Finset G) (t : G) : mass D Q t ≤ Q.card := by
  apply le_trans (Finset.card_le_card (s := Finset.univ.filter fun j => t-j ∈ D ∧ j ∈ Q)
    (t := Q) ?_) le_rfl
  intro j hj
  exact ((Finset.mem_filter.mp hj).2).2

private theorem moments (D Q : Finset G) (p : ℕ) (hd : D.card = p+1) (hq : Q.card = p+1)
    (hD : ∀ r : G, r ≠ 0 → Difference.autocorrelation D r = 1) :
    (∑ t, (mass D Q t : ℤ) = ((p : ℤ)+1)^2) ∧
    (∑ t, (mass D Q t : ℤ)^2 = ((p : ℤ)+1)^2 + (p : ℤ)^2 + p) := by
  constructor
  · simp_rw [mass_eq]
    rw [Difference.first_moment, hd, hq]
    push_cast
    ring
  · simp_rw [mass_eq]
    have hgram := Difference.gram_of_difference D (p+1) hd hD
    rw [← Difference.gram_reverse] at hgram
    have he := Moments.second_moment_of_gram ((Set.indicator (D: Set G) (1 : G → ℤ))) ((Set.indicator (Q: Set G) (1 : G → ℤ)))
      ((p+1 : ℕ)-1 : ℤ) (p+1 : ℕ)
      (by intro i; simp [Set.indicator]) (by rw [Difference.sum_ind, hq])
    have hc : ((p+1 : ℕ)-1 : ℤ) = (p : ℤ) := by omega
    have hgz : (((p+1 : ℕ) : ℤ)-1) = ((p+1 : ℕ)-1 : ℤ) := by push_cast; omega
    rw [hgz] at hgram
    have hfinal := he hgram
    rw [hc] at hfinal
    push_cast at hfinal
    convert hfinal using 1 <;> ring


variable {p : ℕ} [Fact p.Prime]
private theorem line_weight (D : Finset G) (t : G) : (Finset.univ.filter fun i => ((Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p)) t)) i ≠ 0 ∨ ((Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p)) t)) i ≠ 0).card = D.card := by
  simp only [or_self]
  have he : ∀ j, (Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p)) t) j ≠ 0 ↔ t-j ∈ D := by
    intro j
    by_cases hj : t-j ∈ D <;> simp [Matrix.circulant_apply, Set.indicator, Set.indicator, hj]
  simp_rw [he]
  apply Finset.card_bij (fun j _ => t-j)
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro i _ j _ hh
    exact (Equiv.subLeft t).injective hh
  · intro j hj
    exact ⟨t-j, by simp [hj], by simp⟩

private theorem field_gram (D : Finset G) (hcard : D.card = p+1)
    (hD : ∀ r : G, r ≠ 0 → Difference.autocorrelation D r = 1) :
    Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ZMod p))) * (Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ZMod p)))).transpose =
      Matrix.of (fun _ _ => (1 : ZMod p)) := by
  ext i j
  have he := Difference.gram_entry D i j
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) he
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.circulant_apply,
    Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hcast
  have hind (x : G) : ((Set.indicator (D : Set G) (1 : G → ℤ)) x : ZMod p) =
      Set.indicator (D : Set G) (1 : G → ZMod p) x := by
    by_cases hx : x ∈ D <;> simp [Set.indicator, hx]
  simp only [hind] at hcast
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.circulant_apply, Matrix.of_apply]
  rw [hcast]
  by_cases hij : i=j
  · subst j
    simp [Difference.autocorrelation, hcard]
  · simp [hD (i-j) (sub_ne_zero.mpr hij)]

private theorem line_image (D : Finset G) (hcard : D.card = p+1)
    (hD : ∀ r : G, r ≠ 0 → Difference.autocorrelation D r = 1) (t : G) :
    (Matrix.circulant ((Set.indicator (D: Set G) (1 : G → ZMod p)))).mulVec ((Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p)) t)) = 1 := by
  ext i
  have h := congrArg (fun C : Matrix G G (ZMod p) => C i t) (field_gram D hcard hD)
  exact h

private theorem row_sum (Q : Finset G) (hcard : Q.card = p + 1) :
    (Matrix.circulant (Set.indicator (Q : Set G) (1 : G → ZMod p))).mulVec
      (1 : G → ZMod p) = 1 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, Pi.one_apply, mul_one]
  have hs : ∑ j, Set.indicator (Q : Set G) (1 : G → ZMod p) (i-j) =
      ∑ j, Set.indicator (Q : Set G) (1 : G → ZMod p) j :=
    Fintype.sum_equiv (Equiv.subLeft i) _ _ (by intro t; rfl)
  rw [hs]
  have he : ∑ j, Set.indicator (Q : Set G) (1 : G → ZMod p) j = (Q.card : ZMod p) := by
    simp [Set.indicator]
  rw [he, hcard]
  simp

private theorem line_dot (D Q : Finset G) (t : G) :
    dotProduct ((Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p)) t)) (Set.indicator (Q : Set G) (1 : G → ZMod p)) =
      (mass D Q t : ZMod p) := by
  simp only [dotProduct, Matrix.circulant_apply, mass, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hd : t-j ∈ D <;> by_cases hq : j ∈ Q <;> simp [Set.indicator, hd, hq]

private theorem exists_logical (hp : 2 < p) (D Q : Finset G)
    (hcard : D.card = p + 1) (hqcard : Q.card = p + 1)
    (hD : ∀ r : G, r ≠ 0 → Difference.autocorrelation D r = 1) :
    ∃ v : (G → ZMod p) × (G → ZMod p),
      (∀ w : (G → ZMod p) × (G → ZMod p),
        (∃ c, w =
          (Matrix.vecMul c (Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p))),
           Matrix.vecMul c (Matrix.circulant (Set.indicator (Q : Set G) (1 : G → ZMod p)) *
             Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p))))) →
        dotProduct v.1 w.2 - dotProduct v.2 w.1 = 0) ∧
      v ∉ {v | ∃ c, v =
        (Matrix.vecMul c (Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p))),
         Matrix.vecMul c (Matrix.circulant (Set.indicator (Q : Set G) (1 : G → ZMod p)) *
           Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p))))} ∧
      (Finset.univ.filter fun i => v.1 i ≠ 0 ∨ v.2 i ≠ 0).card ≤ p + 1 := by
  have hmm := moments D Q p hcard hqcard hD
  have hdelta : ∑ i, ((Set.indicator (D : Set G) (1 : G → ℕ)) i : ℤ) = (p : ℤ)+1 := by
    simpa [Set.indicator, Set.indicator, hcard] using Difference.sum_ind D
  obtain ⟨t, ht⟩ := Moments.moments_force_nonzero_residue hp (mass D Q) ((Set.indicator (D : Set G) (1 : G → ℕ)))
    (by intro i; simp [Set.indicator]; split_ifs <;> omega)
    (by intro i; exact (mass_le D Q i).trans_eq hqcard) hdelta hmm.1 hmm.2
  refine ⟨((Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p)) t), (Matrix.circulant (Set.indicator (D : Set G) (1 : G → ZMod p)) t)), ?_, ?_, ?_⟩
  · exact Linear.diagonal_central _ _ _ (line_image D hcard hD t) (row_sum Q hqcard)
  · apply Linear.nonstabilizer_of_separator
    rw [line_dot]
    intro he
    have he' : (mass D Q t : ZMod p) = ((Set.indicator (D : Set G) (1 : G → ℕ)) t : ZMod p) := by
      simpa [Matrix.circulant_apply, Set.indicator, Set.indicator, Set.indicator] using he
    have hδ : (Set.indicator (D : Set G) (1 : G → ℕ)) t < p := by have := (Fact.out : p.Prime).two_le; by_cases ht : t ∈ D <;> simp [Set.indicator, ht] <;> omega
    have hh := (ZMod.natCast_eq_natCast_iff' (mass D Q t) ((Set.indicator (D : Set G) (1 : G → ℕ)) t) p).mp he'
    rw [Nat.mod_eq_of_lt hδ] at hh
    exact ht hh
  · rw [line_weight, hcard]

end Generic

theorem result : claim := by
  intro p hp hodd α hα
  letI : Fact p.Prime := ⟨hp⟩
  let D : Finset (Fin (p ^ 2 + p + 1)) := Finset.univ.filter fun i =>
    Algebra.trace (ZMod p) (GaloisField p 3) (α ^ i.val) = 0
  let Q : Finset (Fin (p ^ 2 + p + 1)) := Finset.univ.filter fun i =>
    Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (2*i.val)) = 0
  have hSinger := D5.S3.Geometry.FiniteGeometry.SingerTracePlane.result α hα
  have hD : ∀ r : Fin (p ^ 2 + p + 1), r ≠ 0 → Difference.autocorrelation D r = 1 := by
    intro r hr
    simpa [Difference.autocorrelation, D] using hSinger.2.2.1 r hr
  obtain ⟨v, hc, hs, hw⟩ := Generic.exists_logical hodd D Q hSinger.1 hSinger.2.1 hD
  have hH : Set.indicator (D : Set (Fin (p ^ 2 + p + 1))) (1 : Fin (p ^ 2 + p + 1) → ZMod p) = tauH α := by
    ext i
    simp [Set.indicator, D, tauH]
  have hQ : Set.indicator (Q : Set (Fin (p ^ 2 + p + 1))) (1 : Fin (p ^ 2 + p + 1) → ZMod p) = tauQ α := by
    ext i
    simp [Set.indicator, Q, tauQ]
  rw [hH, hQ] at hc hs
  exact ⟨v, hc, hs, hw⟩

end D5.S3.Quantum.Information.SingerQuadricQuditDistanceBound
