/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubOrientation
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub orientation identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubHomogeneous
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
open FiolDoubleHubEndpoint
open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiolDoubleHub
namespace Orientation

private noncomputable def incidence {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (v : V) : ℕ :=
  (Finset.univ.filter (fun e => s e=v)).card +
    (Finset.univ.filter (fun e => t e=v)).card

private def reverseSrc {V E : Type} (s t : E → V) (f : E → Bool) (e : E) : V :=
  if f e then t e else s e
private def reverseTgt {V E : Type} (s t : E → V) (f : E → Bool) (e : E) : V :=
  if f e then s e else t e
private def reverseSplit {E : Type} (n k : E → ℕ) (f : E → Bool) (e : E) : ℕ :=
  if f e then n e-k e else k e

private theorem reverseSplit_mem {E : Type} [Fintype E] [DecidableEq E] (n k : E → ℕ) (f : E → Bool)
    (hk : k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n) :
    reverseSplit n k f ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro e
  have h := Fintype.mem_piFinset.mp hk e
  change k e ∈ Finset.Icc 1 (n e-1) at h
  change reverseSplit n k f e ∈ Finset.Icc 1 (n e-1)
  rw [Finset.mem_Icc] at *
  unfold reverseSplit
  cases hfe : f e <;> simp [hfe] <;> omega

private theorem reverseSplit_twice {E : Type} [Fintype E] [DecidableEq E] (n k : E → ℕ) (f : E → Bool)
    (hk : k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n) :
    reverseSplit n (reverseSplit n k f) f=k := by
  funext e
  have h := Fintype.mem_piFinset.mp hk e
  change k e ∈ Finset.Icc 1 (n e-1) at h
  have hle : k e≤n e := by have := (Finset.mem_Icc.mp h).2;omega
  cases hfe : f e <;> simp [reverseSplit,hfe,Nat.sub_sub_self hle]

private theorem incidence_reverse {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (f : E → Bool) (v : V) :
    incidence (reverseSrc s t f) (reverseTgt s t f) v=incidence s t v := by
  classical
  simp only [incidence,Finset.card_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  cases hfe : f e <;> simp [reverseSrc,reverseTgt,hfe,add_comm]

private theorem mass_reverse {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (n k : E → ℕ) (f : E → Bool)
    (hk : k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n) (v : V) :
    D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass
      (reverseSrc s t f) (reverseTgt s t f) n (reverseSplit n k f) v =
    D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass s t n k v := by
  classical
  simp only [D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass,
    Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have h := Fintype.mem_piFinset.mp hk e
  change k e ∈ Finset.Icc 1 (n e-1) at h
  have hle : k e≤n e := by have := (Finset.mem_Icc.mp h).2;omega
  cases hfe : f e <;> simp [reverseSrc,reverseTgt,reverseSplit,hfe,Nat.sub_sub_self hle,add_comm]

-- This is the original factorial vertex formula after the finite product
-- regrouping physicalWeight_by_edges. No source weight is assigned by fiat.
private noncomputable def weight {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (n k : E → ℕ) : ℝ :=
  (∏ e : E,(Nat.choose (2*n e) (2*k e):ℝ)*J (k e)*J (n e-k e)) *
    ∏ v : V,(Nat.factorial (D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass s t n k v-1):ℝ)/
      (Nat.factorial (D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass s t n k v-
        incidence s t v+2):ℝ)

private theorem weight_reverse {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (n k : E → ℕ) (f : E → Bool)
    (hk : k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n) :
    weight (reverseSrc s t f) (reverseTgt s t f) n (reverseSplit n k f)=weight s t n k := by
  classical
  unfold weight
  simp_rw [mass_reverse s t n k f hk,incidence_reverse s t f]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  have h := Fintype.mem_piFinset.mp hk e
  change k e ∈ Finset.Icc 1 (n e-1) at h
  have hle : k e≤n e := by have := (Finset.mem_Icc.mp h).2;omega
  cases hfe : f e
  · simp [reverseSplit,hfe]
  · have hmul : 2*n e-2*k e=2*(n e-k e) := by omega
    have hb : (2*n e).choose (2*(n e-k e))=(2*n e).choose (2*k e) := by
      rw [←hmul,Nat.choose_symm (by omega)]
    simp only [reverseSplit,hfe,ite_true,Nat.sub_sub_self hle,hb]
    ring

private noncomputable def vertexFactor {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (n k : E → ℕ) (v : V) : ℝ :=
  (Nat.factorial (D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass s t n k v-1):ℝ)/
    (Nat.factorial (D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass s t n k v-
      incidence s t v+2):ℝ) *
    (∏ e ∈ Finset.univ.filter (fun e => s e=v),J (k e)) *
    (∏ e ∈ Finset.univ.filter (fun e => t e=v),J (n e-k e))

private noncomputable def physical {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (n k : E → ℕ) : ℝ :=
  (∏ e : E,(Nat.choose (2*n e) (2*k e):ℝ)) * ∏ v : V,vertexFactor s t n k v

private theorem physical_eq_weight {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (n k : E → ℕ) : physical s t n k=weight s t n k := by
  classical
  unfold physical vertexFactor weight
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.prod_fiberwise,Finset.prod_fiberwise]
  ring

noncomputable def polynomial {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (n : E → ℕ) : Polynomial ℝ :=
  ∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n,
    Polynomial.C (physical s t n k) *
      ∏ v : V,(1+Polynomial.C ((-1:ℝ)^incidence s t v)*
        Polynomial.X^(D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass s t n k v))

theorem polynomial_reverse {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (s t : E → V) (n : E → ℕ) (f : E → Bool) :
    polynomial (reverseSrc s t f) (reverseTgt s t f) n=polynomial s t n := by
  classical
  unfold polynomial
  symm
  apply Finset.sum_bij (fun k _ => reverseSplit n k f)
  · intro k hk
    exact reverseSplit_mem n k f hk
  · intro k hk l hl he
    have hh := congrArg (fun q => reverseSplit n q f) he
    simpa only [reverseSplit_twice n k f hk,reverseSplit_twice n l f hl] using hh
  · intro k hk
    exact ⟨reverseSplit n k f,reverseSplit_mem n k f hk,reverseSplit_twice n k f hk⟩
  · intro k hk
    rw [physical_eq_weight,physical_eq_weight,weight_reverse s t n k f hk]
    simp_rw [incidence_reverse s t f,mass_reverse s t n k f hk]

private theorem actual_polynomial (m : ℕ) (n : Edge m → ℕ) :
    polynomial (src : Edge m → Vertex m) tgt n=allVertexSource n := by
  rfl

-- The reversed arrows use the same actual edge totals and the original
-- physical factorial formula. Equality holds after the complete split sum.
theorem actual_arrow_sum_invariance (m : ℕ) (n : Edge m → ℕ)
    (f : Edge m → Bool) :
    polynomial (reverseSrc (src : Edge m → Vertex m) tgt f)
      (reverseTgt src tgt f) n=allVertexSource n := by
  rw [polynomial_reverse,actual_polynomial]

end Orientation
end FiolDoubleHub

end D5.S3.Zeros.LeeYang
