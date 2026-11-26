/- GID: D5/S3/HomologicalAlgebra/CocycleDiagonalQuadratic
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cocycle diagonals supply the quadratic term for the next coordinate. -/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-! Diagonals of two-torsion group cocycles and their quadratic expansions. -/

set_option autoImplicit false

public section

namespace D5.S3.HomologicalAlgebra.CocycleDiagonalQuadratic

/-- The diagonal of a normalized, 2-torsion-valued cocycle on an elementary
2-group vanishes at zero. Its polarization is the cocycle's skew difference
and is additive in both variables. The ambient coefficient group may contain
elements of other orders. -/
theorem diagonal_quadratic {A M : Type*} [AddCommGroup A] [AddCommGroup M]
    (hA : ∀ a : A, a + a = 0) (U : A → A → M)
    (hn : ∀ a, U 0 a = 0)
    (hc : ∀ a b c, U a b + U (a + b) c = U b c + U a (b + c))
    (htwo : ∀ a b, U a b + U a b = 0) :
    let B := QuadraticMap.polar (fun a => U a a)
    U 0 0 = 0 ∧
      (∀ a b, B a b = U a b - U b a) ∧
      (∀ a b c, B (a + b) c = B a c + B b c) ∧
      (∀ a b c, B a (b + c) = B a b + B a c) := by
  dsimp only
  have hpolar (a b : A) :
      QuadraticMap.polar (fun x => U x x) a b = U a b - U b a := by
    have hb : b + (a + b) = a := by
      rw [add_comm a b, ← add_assoc, hA b, zero_add]
    have hab := hc a b (a + b)
    have hbb := hc b b a
    rw [hb] at hab
    simp only [hA b, hn a, add_zero, add_comm b a] at hbb
    unfold QuadraticMap.polar
    linear_combination (norm := abel) hab - hbb - htwo a b
  have hadd (a b c : A) :
      QuadraticMap.polar (fun x => U x x) (a + b) c =
        QuadraticMap.polar (fun x => U x x) a c +
          QuadraticMap.polar (fun x => U x x) b c := by
    have habc := hc a b c
    have hacb := hc a c b
    have hcab := hc c a b
    rw [add_comm c b] at hacb
    rw [add_comm c a] at hcab
    simp only [hpolar]
    linear_combination (norm := abel) habc - hacb + hcab
  refine ⟨hn 0, hpolar, hadd, ?_⟩
  intro a b c
  rw [QuadraticMap.polar_comm _ a (b + c), QuadraticMap.polar_comm _ a b,
    QuadraticMap.polar_comm _ a c, hadd]

/-- The mixed diagonal in one step of an elementary two-group product
decomposition is quadratic. The joint cocycle equation allows the
off-diagonal cochain to be corrected to take values in the 2-torsion. -/
theorem mixed_diagonal_quadratic {A M : Type*} [AddCommGroup A] [AddCommGroup M]
    (hA : ∀ a : A, a + a = 0) (half : ∀ m : M, ∃ k, k + k = m)
    (u : A → A → M) (v : A → M)
    (hu0 : ∀ a, u 0 a = 0) (hv0 : v 0 = 0)
    (hu : ∀ a b c, u a b + u (a + b) c = u b c + u a (b + c))
    (hjoint : ∀ a b, u a b + u a b + (v b - v (a + b) + v a) = 0) :
    let q := fun a => u a a + v a
    q 0 = 0 ∧ (∀ a, q a + q a = 0) ∧
      ∀ a b c, QuadraticMap.polar q (a + b) c =
        QuadraticMap.polar q a c + QuadraticMap.polar q b c := by
  dsimp only
  have hex (a : A) : ∃ k : M, (a = 0 → k = 0) ∧ k + k = -v a := by
    by_cases ha : a = 0
    · exact ⟨0, fun _ => rfl, by simp [ha, hv0]⟩
    · obtain ⟨k, hk⟩ := half (-v a)
      exact ⟨k, fun contra => (ha contra).elim, hk⟩
  choose k hk0 hk using hex
  have kzero := hk0 0 rfl
  let U (a b : A) := u a b - (k b - k (a + b) + k a)
  have hU0 (a : A) : U 0 a = 0 := by simp [U, hu0, kzero]
  have hU (a b c : A) : U a b + U (a + b) c = U b c + U a (b + c) := by
    simp only [U, add_assoc]
    linear_combination (norm := abel) hu a b c
  have htwo (a b : A) : U a b + U a b = 0 := by
    dsimp only [U]
    linear_combination (norm := abel) hjoint a b - hk b + hk (a + b) - hk a
  have hdiag (a : A) : U a a = u a a + v a := by
    simp only [U, hA a, kzero, sub_zero]
    linear_combination (norm := abel) -hk a
  have hq : (fun a => U a a) = (fun a => u a a + v a) := funext hdiag
  have hquadratic := diagonal_quadratic hA U hU0 hU htwo
  change U 0 0 = 0 ∧ _ ∧ _ ∧ _ at hquadratic
  have ha := hquadratic.2.2.1
  rw [hq] at ha
  exact ⟨by rw [← hdiag, hU0], fun a => by rw [← hdiag, htwo], ha⟩

open scoped BigOperators in
/-- Evaluating a two-torsion quadratic function on the sum of a set of
coordinate vectors uses only its values at single coordinates and its
polarization at pairs of distinct coordinates. -/
theorem quadratic_sum_pairs {V M ι : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup M] [DecidableEq ι] (q : V → M) (hq0 : q 0 = 0)
    (htwo : ∀ x, q x + q x = 0)
    (hpolar : ∀ x y z : V, QuadraticMap.polar q (x + y) z =
      QuadraticMap.polar q x z + QuadraticMap.polar q y z)
    (s : Finset ι) (v : ι → V) :
    q (∑ i ∈ s, v i) = (∑ i ∈ s, q (v i)) +
      ∑ p ∈ s.sym2 with ¬p.IsDiag, QuadraticMap.polarSym2 q (p.map v) := by
  let K := AddSubgroup.torsionBy M 2
  let : Module (ZMod 2) K := AddSubgroup.torsionBy.zmodModule
  let f (x : V) : K := ⟨q x, AddSubgroup.torsionBy.nsmul_iff.mpr (by rw [two_nsmul, htwo])⟩
  have hzero : f 0 = 0 := Subtype.ext hq0
  have ha (x y z : V) : QuadraticMap.polar f (x + y) z =
      QuadraticMap.polar f x z + QuadraticMap.polar f y z := Subtype.ext (hpolar x y z)
  have hbit (c : ZMod 2) : c = 0 ∨ c = 1 := by
    revert c
    decide +kernel
  let Q := QuadraticMap.ofPolar f (fun c x => by
    rcases hbit c with h | h <;> simp [h, hzero])
    ha (fun c x y => by
      rcases hbit c with h | h <;> simp [h, QuadraticMap.polar, hzero])
  have hval (p : Sym2 V) : K.subtype (QuadraticMap.polarSym2 (Q : V → K) p) =
      QuadraticMap.polarSym2 q p := by
    induction p using Sym2.ind with
    | h x y =>
      simp only [QuadraticMap.polarSym2_sym2Mk]
      rfl
  have h := congrArg K.subtype (Q.map_sum s v)
  have hq (x : V) : K.subtype (Q x) = q x := rfl
  simpa only [map_add, map_sum, hval, hq] using h

end D5.S3.HomologicalAlgebra.CocycleDiagonalQuadratic
