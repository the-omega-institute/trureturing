/- GID: D5/S1/Dynamics/Symbolic/KhetanSixCellPeriodicity
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Primitive normalization of genuine line divisors and the full given-tiling six-cell consumer. -/

import D5.S1.Dynamics.Symbolic.KhetanDirectionalCoprimality
import D5.S1.Dynamics.Symbolic.KhetanLineFactorCancellation

/-!
The tile is an arbitrary six-element finite subset of the integer lattice.
Its integer differences span the whole lattice, and the complement is the
given predicate, with its actual exact-cover equation. The conclusion retains
that predicate and its actual shift orbit closure.

Line directions in `OnlyLineDirection` need not be primitive. A positive gcd
decomposition and the injective Laurent substitution T ↦ T^g preserve the
literal embedded divisor. A nonzero root and a g-th root prove that this
substitution also preserves nonunit status. Thus the two-direction geometric
consumer receives genuine primitive line divisors, without assuming roots,
cancellation, irreducibility or localized coprimality.

The at-most-one-direction branch applies the integer periodizer supplier to
the indicator of this same complement. The negative exact-cover mask has
coefficient one at every negative tile point and acts on that indicator as
the constant one. The branch split includes masks without any line divisor:
the fixed primitive vector (1,0) then satisfies `OnlyLineDirection` vacuously.

This is source for the question in arXiv:2607.09830v2, §3.5, using the general
finitary integral periodizer route described in arXiv:2301.05232v1, Theorem 2.
It is not a claim of kernel verification, acceptance or literature novelty.
-/

/-
The integer gcd normalization pattern is shared with boonsuan/nivat,
revision 4e3614024227acd273c3e8ab41df92c2709e5ab0,
Nivat/Core/Lattice.lean, exists_lattice_basis_for_nonzero. The present proof
uses Mathlib's Int.exists_gcd_one directly and does not port the basis theorem.
The action and product-difference suppliers retain their upstream attribution.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanSixCellPeriodicity

open scoped BigOperators
open D5.S1.Dynamics.Symbolic.KhetanLaurent
open D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra
open D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
open D5.S1.Dynamics.Symbolic.KhetanDirectionalCoprimality
open D5.S1.Dynamics.Symbolic.KhetanLatticeGeometry

local notation "Lattice" => D5.S1.Dynamics.Symbolic.KhetanLaurent.Lattice

private def exponentScaling (g : ℕ) : ℤ →+ ℤ where
  toFun n := (g : ℤ) * n
  map_zero' := mul_zero _
  map_add' _ _ := mul_add _ _ _

private noncomputable def rescaleLaurent (g : ℕ) :
    LaurentPolynomial ℂ →+* LaurentPolynomial ℂ :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (exponentScaling g)

private theorem rescale_single (g : ℕ) (n : ℤ) (a : ℂ) :
    rescaleLaurent g (AddMonoidAlgebra.single n a) =
      AddMonoidAlgebra.single ((g : ℤ) * n) a := by
  change AddMonoidAlgebra.mapDomain (exponentScaling g)
    (AddMonoidAlgebra.single n a) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

private theorem rescale_injective (g : ℕ) (hg : 0 < g) :
    Function.Injective (rescaleLaurent g) := by
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  have hi : Function.Injective (exponentScaling g) := by
    intro m n h
    exact mul_left_cancel₀ hg0 h
  exact AddMonoidAlgebra.mapDomain_injective hi

private theorem line_rescale (u : Lattice) (g : ℕ) (A : LaurentPolynomial ℂ) :
    lineLaurent u (rescaleLaurent g A) = lineLaurent ((g : ℤ) • u) A := by
  induction A using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add A B hA hB => simp only [map_add, hA, hB]
  | single n a =>
    rw [rescale_single, line_laurent_single, line_laurent_single, smul_smul,
      mul_comm (g : ℤ) n]

private theorem eval_rescale (g : ℕ) (A : LaurentPolynomial ℂ) (β : ℂˣ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) β (rescaleLaurent g A) =
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (β ^ g) A := by
  induction A using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add A B hA hB => simp only [map_add, hA, hB]
  | single n a =>
    rw [rescale_single, LaurentPolynomial.single_eq_C_mul_T,
      LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.single_eq_C_mul_T,
      LaurentPolynomial.eval₂_C_mul_T]
    simp only [zpow_mul, zpow_natCast]

/-- Root extraction is the same polynomial clearing argument as the private
supplier in `KhetanLineFactorCancellation`. It is consumed only by normalization
here; no private declaration in another module is addressed by a generated name. -/
private theorem nonzero_laurent_root (A : LaurentPolynomial ℂ)
    (hA : A ≠ 0) (hunit : ¬ IsUnit A) :
    ∃ root : ℂˣ, LaurentPolynomial.eval₂ (RingHom.id ℂ) root A = 0 := by
  obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow A
  have hq0 : q ≠ 0 := by
    intro hz
    have hAz : A * LaurentPolynomial.T (n : ℤ) = 0 := by
      rw [← hq, hz, map_zero]
    exact (mul_ne_zero hA (LaurentPolynomial.isUnit_T (n : ℤ)).ne_zero) hAz
  obtain ⟨s, hs, hnotX⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq0 0
  have hs' : q = Polynomial.X ^ q.rootMultiplicity 0 * s := by simpa using hs
  have hs0 : s.coeff 0 ≠ 0 := by
    simpa only [map_zero, sub_zero, Polynomial.X_dvd_iff] using hnotX
  have hdegree : s.natDegree ≠ 0 := by
    intro hdeg
    have hqunit : IsUnit q.toLaurent := by
      rw [hs', Polynomial.eq_C_of_natDegree_eq_zero hdeg, map_mul, map_pow,
        Polynomial.toLaurent_X, Polynomial.toLaurent_C]
      exact ((LaurentPolynomial.isUnit_T (1 : ℤ)).pow _).mul
        ((isUnit_iff_ne_zero.mpr hs0).map LaurentPolynomial.C)
    rw [hq] at hqunit
    exact hunit ((Commute.all A (LaurentPolynomial.T (n : ℤ))).isUnit_mul_iff.mp hqunit).1
  obtain ⟨z, hz⟩ := Complex.exists_root
    (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree))
  have hsroot' : Polynomial.eval₂ (RingHom.id ℂ) z s = 0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval₂_id] using hz
  have hz0 : z ≠ 0 := by
    intro heq
    apply hs0
    simpa only [heq, Polynomial.eval₂_at_zero, RingHom.id_apply] using hsroot'
  let root : ℂˣ := Units.mk0 z hz0
  have hsroot : Polynomial.eval₂ (RingHom.id ℂ) (root : ℂ) s = 0 := by
    simpa only [root, Units.val_mk0] using hsroot'
  have hqroot : LaurentPolynomial.eval₂ (RingHom.id ℂ) root q.toLaurent = 0 := by
    rw [LaurentPolynomial.eval₂_toLaurent, hs', Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, hsroot, mul_zero]
  have hprod : LaurentPolynomial.eval₂ (RingHom.id ℂ) root A *
      LaurentPolynomial.eval₂ (RingHom.id ℂ) root (LaurentPolynomial.T (n : ℤ)) = 0 := by
    rw [← map_mul, ← hq]
    exact hqroot
  refine ⟨root, (mul_eq_zero.mp hprod).resolve_right ?_⟩
  exact ((LaurentPolynomial.isUnit_T (n : ℤ)).map
    (LaurentPolynomial.eval₂ (RingHom.id ℂ) root)).ne_zero

private theorem rescale_nonunit (g : ℕ) (hg : 0 < g)
    (A : LaurentPolynomial ℂ) (hA : A ≠ 0) (hunit : ¬ IsUnit A) :
    ¬ IsUnit (rescaleLaurent g A) := by
  obtain ⟨α, hα⟩ := nonzero_laurent_root A hA hunit
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (α : ℂ) hg
  have hz0 : z ≠ 0 := by
    intro hzero
    have hα0 : (α : ℂ) = 0 := by
      rw [← hz, hzero, zero_pow (Nat.ne_of_gt hg)]
    exact α.ne_zero hα0
  let β : ℂˣ := Units.mk0 z hz0
  have hβα : β ^ g = α := by
    apply Units.ext
    exact hz
  have heval : LaurentPolynomial.eval₂ (RingHom.id ℂ) β (rescaleLaurent g A) = 0 := by
    rw [eval_rescale, hβα]
    exact hα
  intro hunitB
  have h := hunitB.map (LaurentPolynomial.eval₂ (RingHom.id ℂ) β)
  rw [heval] at h
  exact not_isUnit_zero h

/-- Normalize a genuine line divisor even when its original direction is not
primitive. The output factor has exactly the same image in the lattice ring.
Positive exponent scaling keeps negative exponents and all finite support;
its injectivity and a lifted nonzero root supply nonzeroness and nonunitness. -/
theorem primitive_line_divisor
    (P : AddMonoidAlgebra ℂ Lattice) (v : Lattice) (hv : v ≠ 0)
    (A : LaurentPolynomial ℂ) (hA : A ≠ 0) (hunit : ¬ IsUnit A)
    (hdiv : lineLaurent v A ∣ P) :
    ∃ (u : Lattice) (g : ℕ) (B : LaurentPolynomial ℂ),
      0 < g ∧ Primitive u ∧ v = (g : ℤ) • u ∧ B ≠ 0 ∧ ¬ IsUnit B ∧
        lineLaurent u B = lineLaurent v A ∧ lineLaurent u B ∣ P := by
  have hg : 0 < Int.gcd v.1 v.2 := by
    apply Int.gcd_pos_iff.mpr
    by_contra! hz
    exact hv (Prod.ext hz.1 hz.2)
  obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hg
  let u : Lattice := (a, b)
  let g : ℕ := Int.gcd v.1 v.2
  have hvu : v = (g : ℤ) • u := by
    apply Prod.ext
    · change v.1 = (g : ℤ) * a
      simpa only [g, mul_comm] using ha
    · change v.2 = (g : ℤ) * b
      simpa only [g, mul_comm] using hb
  have hB : rescaleLaurent g A ≠ 0 := by
    intro hz
    apply hA
    apply rescale_injective g hg
    simpa only [map_zero] using hz
  have hembed : lineLaurent u (rescaleLaurent g A) = lineLaurent v A := by
    rw [line_rescale, ← hvu]
  refine ⟨u, g, rescaleLaurent g A, hg, hab, hvu, hB,
    rescale_nonunit g hg A hA hunit, hembed, ?_⟩
  rw [hembed]
  exact hdiv

private noncomputable def integerIndicator (T : Lattice → Prop) : Configuration ℤ :=
  fun x => (indicator T x : ℤ)

private theorem integer_indicator_finite (T : Lattice → Prop) :
    FiniteRange (integerIndicator T) := by
  classical
  have hs : ({0, 1} : Set ℤ).Finite := by simp
  apply hs.subset
  rintro a ⟨x, rfl⟩
  by_cases hx : T x <;> simp [integerIndicator, indicator, hx]

private theorem integer_indicator_cover (F : Finset Lattice) (T : Lattice → Prop)
    (hcover : ExactCover F T) :
    coefficientAct (exactCoverMask F) (integerIndicator T) = fun _ => (1 : ℤ) := by
  classical
  funext x
  rw [exact_cover_mask_act]
  have hc : (∑ f ∈ F, indicator T (x - f)) = (1 : ℕ) := by
    simpa only [exactCoverCount, indicator] using hcover x
  simpa only [integerIndicator, Nat.cast_sum, Nat.cast_one] using
    congrArg (fun n : ℕ => (n : ℤ)) hc

private theorem mask_coefficient_at_tile (F : Finset Lattice) (p : Lattice) (hp : p ∈ F) :
    (exactCoverMask F).coeff (-p) = 1 := by
  classical
  simp only [exactCoverMask, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single_apply]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _hq hqp
    have hneg : -q ≠ -p := fun he => hqp (neg_injective he)
    simp [hneg]
  · exact fun h => (h hp).elim

private theorem predicate_period_of_indicator_period (T : Lattice → Prop) (t : Lattice)
    (hp : ∀ x, indicator T (x + t) = indicator T x) : Period T t := by
  classical
  intro x
  have h := hp x
  by_cases ha : T (x + t) <;> by_cases hb : T x <;> simp_all [indicator]

private theorem common_period_on_closure (T : Lattice → Prop) (t : Lattice)
    (hp : Period T t) :
    ∀ c ∈ closure (Set.range (fun s : Lattice => fun x => indicator T (x + s))),
      ∀ x, c (x + t) = c x := by
  classical
  let shiftT : (Lattice → ℕ) → (Lattice → ℕ) := fun c x => c (x + t)
  have hclosed : IsClosed (Function.fixedPoints shiftT) :=
    isClosed_fixedPoints (continuous_pi fun x => continuous_apply (x + t))
  have hsub : Set.range (fun s : Lattice => fun x => indicator T (x + s)) ⊆
      Function.fixedPoints shiftT := by
    rintro c ⟨s, rfl⟩
    change (fun x => indicator T (x + t + s)) = (fun x => indicator T (x + s))
    funext x
    rw [show x + t + s = (x + s) + t by abel]
    unfold indicator
    rw [propext (hp (x + s))]
  intro c hc x
  have hf : shiftT c = c := closure_minimal hsub hclosed hc
  exact congrFun hf x

/-- The full six-cell consumer: the given exact-cover complement itself has a
nonzero period, shared by every point of its actual shift orbit closure.
No line-factor, cancellation or coprimality hypothesis appears in the telescope. -/
theorem six_cell_exact_cover_periodic
    (F : Finset Lattice) (T : Lattice → Prop)
    (hF : F.card = 6) (hspan : FullDifferenceSpan F) (hcover : ExactCover F T) :
    ∃ t : Lattice, t ≠ 0 ∧ Period T t ∧
      ∀ c ∈ closure (Set.range (fun s : Lattice => fun x => indicator T (x + s))),
        ∀ x, c (x + t) = c x := by
  classical
  let P : AddMonoidAlgebra ℂ Lattice :=
    AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℂ) (exactCoverMask F)
  by_cases hone : ∃ u : Lattice, Primitive u ∧ OnlyLineDirection P u
  · obtain ⟨u, hu, hline⟩ := hone
    have hFnonempty : F.Nonempty := Finset.card_pos.mp (by omega)
    have hmask : exactCoverMask F ≠ 0 := by
      obtain ⟨p, hp⟩ := hFnonempty
      intro hz
      have hc := mask_coefficient_at_tile F p hp
      rw [hz] at hc
      simpa using hc
    obtain ⟨t, ht, hp⟩ := integer_one_direction_periodizer_periodic
      (integerIndicator T) (integer_indicator_finite T) (exactCoverMask F) hmask 1
      (integer_indicator_cover F T hcover) u (Int.isCoprime_iff_gcd_eq_one.mpr hu) hline
    have hnat : ∀ x, indicator T (x + t) = indicator T x := by
      intro x
      have hi := hp x
      change (indicator T (x + t) : ℤ) = (indicator T x : ℤ) at hi
      exact_mod_cast hi
    have hprop : Period T t := predicate_period_of_indicator_period T t hnat
    exact ⟨t, ht, hprop, common_period_on_closure T t hprop⟩
  · have hnot (u : Lattice) (hu : Primitive u) : ¬ OnlyLineDirection P u := by
      intro hline
      exact hone ⟨u, hu, hline⟩
    have he : Primitive ((1 : ℤ), (0 : ℤ)) := by norm_num [Primitive]
    have hfirst := hnot (1, 0) he
    unfold OnlyLineDirection at hfirst
    push_neg at hfirst
    obtain ⟨v, A, hv, hA, hAu, hdivA, _⟩ := hfirst
    obtain ⟨u, g, A₀, _hg, hu, _hvu, hA₀, hA₀u, _hAeq, hdivA₀⟩ :=
      primitive_line_divisor P v hv A hA hAu hdivA
    have hsecond := hnot u hu
    unfold OnlyLineDirection at hsecond
    push_neg at hsecond
    obtain ⟨w, B, hw, hB, hBu, hdivB, huv⟩ := hsecond
    obtain ⟨v₀, k, B₀, _hk, hv₀, hwv₀, hB₀, hB₀u, _hBeq, hdivB₀⟩ :=
      primitive_line_divisor P w hw B hB hBu hdivB
    have hdet : det u v₀ ≠ 0 := by
      intro hz
      apply huv
      have hscale : det u w = (k : ℤ) * det u v₀ := by
        rw [hwv₀]
        change u.1 * ((k : ℤ) * v₀.2) - u.2 * ((k : ℤ) * v₀.1) =
          (k : ℤ) * (u.1 * v₀.2 - u.2 * v₀.1)
        ring
      change det u w = 0
      rw [hscale, hz, mul_zero]
    obtain ⟨t, ht, hclosure⟩ :=
      KhetanLineFactorCancellation.two_line_factors_orbit_closure_periodic
        (RingHom.id ℂ) F T u v₀ hF hu hv₀ hdet A₀ B₀ hA₀ hB₀ hA₀u hB₀u
        hdivA₀ hdivB₀ hspan hcover
    have hself : (fun x => indicator T x) ∈
        closure (Set.range (fun s : Lattice => fun x => indicator T (x + s))) := by
      apply subset_closure
      refine ⟨0, ?_⟩
      funext x
      simp only [add_zero]
    exact ⟨t, ht, predicate_period_of_indicator_period T t
      (hclosure _ hself), hclosure⟩

end D5.S1.Dynamics.Symbolic.KhetanSixCellPeriodicity
