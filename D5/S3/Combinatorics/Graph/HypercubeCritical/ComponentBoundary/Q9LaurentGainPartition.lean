/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Defs, mathlib/module/Mathlib.Data.Finsupp.Multiset, mathlib/module/Mathlib.Algebra.MvPolynomial.Funext]
   utility: none
   digest: A positive Laurent row identity forces the reverse gain and a unique partition into internal axis triples. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PureExteriorLink
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Infinite

/-!
# Laurent coefficients and the direction partition in Q9

The row identity is a hypothesis on one selected parity side. Reversing a
two-step path determines the matched square monomial, and coefficient
multiplicities then determine the partition of the nine axes.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj)
local notation "bitFlip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9IsotropicHuang (parity)
open Q9PureExteriorLink (exteriorDirections)
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

section Evaluation

open scoped BigOperators

variable {n : ℕ}

/-- Evaluate an integer exponent vector at real weights using integer powers. -/
private def laurentMonomial (w : Fin n → ℝ) (v : Fin n → ℤ) : ℝ :=
  ∏ i, w i ^ v i

/-- Evaluate the sum with each exponent counted at its multiset multiplicity. -/
def evaluateLaurent (w : Fin n → ℝ) (s : Multiset (Fin n → ℤ)) : ℝ :=
  (s.map (laurentMonomial w)).sum

private def polynomial (s : Multiset (Fin n →₀ ℕ)) : MvPolynomial (Fin n) ℝ :=
  (s.map fun d => MvPolynomial.monomial d (1 : ℝ)).sum

private theorem coeff_polynomial (s : Multiset (Fin n →₀ ℕ)) (d : Fin n →₀ ℕ) :
    (polynomial s).coeff d = (s.count d : ℝ) := by
  induction s using Multiset.induction_on with
  | empty => simp [polynomial]
  | cons e s ih =>
    rw [polynomial, Multiset.map_cons, Multiset.sum_cons]
    change (MvPolynomial.coeffAddMonoidHom d) (MvPolynomial.monomial e (1 : ℝ) + polynomial s) = _
    rw [map_add]
    change (MvPolynomial.monomial e (1 : ℝ)).coeff d + (polynomial s).coeff d = _
    rw [MvPolynomial.coeff_monomial, ih]
    by_cases h : e = d
    · subst e
      simp [add_comm]
    · simp [h, Ne.symm h]

private theorem polynomial_injective : Function.Injective (polynomial (n := n)) := by
  intro s t h
  apply Multiset.ext'
  intro d
  apply (Nat.cast_inj (R := ℝ)).mp
  simpa only [coeff_polynomial] using
    congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff d) h

/-- Equality on all strictly positive weights determines the exponent multiset. -/
private theorem eq_of_evaluation_eq {s t : Multiset (Fin n → ℤ)}
    (h : ∀ w : Fin n → ℝ, (∀ i, 0 < w i) → evaluateLaurent w s = evaluateLaurent w t) : s = t := by
  classical
  -- Sum the negative parts of both supports in each coordinate.
  let shift (i : Fin n) : ℕ := ∑ v ∈ (s + t).toFinset, (-(v i)).toNat
  have hshift (v : Fin n → ℤ) (hv : v ∈ s + t) (i : Fin n) :
      0 ≤ (shift i : ℤ) + v i := by
    have hvle : (-(v i)).toNat ≤ shift i :=
      Finset.single_le_sum (f := fun u : Fin n → ℤ => (-(u i)).toNat)
        (fun _ _ => Nat.zero_le _) (Multiset.mem_toFinset.mpr hv)
    exact neg_le_iff_add_nonneg.mp ((Int.self_le_toNat (-v i)).trans (Int.ofNat_le.mpr hvle))
  let encode (v : Fin n → ℤ) : Fin n →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun i => ((shift i : ℤ) + v i).toNat
  have hencode (v : Fin n → ℤ) (hv : v ∈ s + t) (i : Fin n) :
      (encode v i : ℤ) = (shift i : ℤ) + v i :=
    Int.toNat_of_nonneg (hshift v hv i)
  have hs (v : Fin n → ℤ) (hv : v ∈ s) : v ∈ s + t := Multiset.mem_add.mpr (Or.inl hv)
  have ht (v : Fin n → ℤ) (hv : v ∈ t) : v ∈ s + t := Multiset.mem_add.mpr (Or.inr hv)
  have eval_shifted (u : Multiset (Fin n → ℤ)) (hu : ∀ v ∈ u, v ∈ s + t)
      (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
      MvPolynomial.eval w (polynomial (u.map encode)) =
        (∏ i, w i ^ shift i) * evaluateLaurent w u := by
    rw [polynomial, Multiset.map_map, map_multiset_sum, Multiset.map_map, evaluateLaurent,
      ← Multiset.sum_map_mul_left]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro v hv
    change MvPolynomial.eval w (MvPolynomial.monomial (encode v) 1) =
      (∏ i, w i ^ shift i) * laurentMonomial w v
    rw [MvPolynomial.eval_monomial, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero (w i)),
      laurentMonomial, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    calc
      w i ^ encode v i = w i ^ (encode v i : ℤ) := (zpow_natCast (w i) _).symm
      _ = w i ^ shift i * w i ^ v i := by
        rw [hencode v (hu v hv) i, zpow_add₀ (ne_of_gt (hw i)), zpow_natCast]
  have hp : polynomial (s.map encode) = polynomial (t.map encode) := by
    apply MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ)) (fun _ => Set.Ioi_infinite _)
    intro w hw
    have hwpos : ∀ i, 0 < w i := fun i => hw i (Set.mem_univ i)
    rw [eval_shifted s hs w hwpos, eval_shifted t ht w hwpos, h w hwpos]
  let decode (d : Fin n →₀ ℕ) (i : Fin n) : ℤ := (d i : ℤ) - (shift i : ℤ)
  have decode_map (u : Multiset (Fin n → ℤ)) (hu : ∀ v ∈ u, v ∈ s + t) :
      (u.map encode).map decode = u := by
    rw [Multiset.map_map]
    refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id u)
    intro v hv
    funext i
    change (encode v i : ℤ) - (shift i : ℤ) = v i
    rw [hencode v (hu v hv) i, add_comm (shift i : ℤ) (v i), add_sub_cancel_right]
  calc
    s = (s.map encode).map decode := (decode_map s hs).symm
    _ = (t.map encode).map decode := congrArg (Multiset.map decode) (polynomial_injective hp)
    _ = t := decode_map t ht

end Evaluation

abbrev Side (C : Finset (Q 9)) (b : Bool) := {x : Q 9 // x ∈ C ∧ parity x = b}
abbrev Exponent := Fin 9 → ℤ

/-- The coordinate vector of the weight on axis `i`. -/
def axis (i : Fin 9) : Exponent := fun r => if r = i then 1 else 0

def squareExponent (i : Fin 9) : Exponent := axis i + axis i

/-- Each ordered pair specifies its unique middle vertex and endpoint by flips. -/
def twoStepPaths (C : Finset (Q 9)) (x : Q 9) : Finset (Fin 9 × Fin 9) :=
  Finset.univ.filter fun p =>
    p.1 ∈ directions C x ∧ p.2 ∈ directions C (bitFlip x p.1) ∧ p.1 ≠ p.2

private theorem mem_twoStepPaths {C : Finset (Q 9)} {x : Q 9} {p : Fin 9 × Fin 9} :
    p ∈ twoStepPaths C x ↔
      p.1 ∈ directions C x ∧ p.2 ∈ directions C (bitFlip x p.1) ∧ p.1 ≠ p.2 := by
  simp only [twoStepPaths, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev PathAt (C : Finset (Q 9)) (x : Q 9) := {p // p ∈ twoStepPaths C x}

variable {C : Finset (Q 9)} {b : Bool}

private theorem flip_parity (x : Q 9) (i : Fin 9) : parity (bitFlip x i) = !parity x :=
  (Bool.not_eq_iff.mpr (cubeParity_ne_of_adj (flip_adj x i))).symm

def pathEnd (x : Side C b) (p : PathAt C x.val) : Side C b :=
  ⟨bitFlip (bitFlip x.val p.val.1) p.val.2, by
    constructor
    · exact (mem_directions C _ _).mp (mem_twoStepPaths.mp p.property).2.1
    · rw [flip_parity, flip_parity, Bool.not_not]
      exact x.property.2⟩

def reversePath (x : Side C b) (p : PathAt C x.val) : PathAt C (pathEnd x p).val :=
  ⟨(p.val.2, p.val.1), by
    refine mem_twoStepPaths.mpr ⟨?_, ?_, (mem_twoStepPaths.mp p.property).2.2.symm⟩
    · apply (mem_directions C _ _).mpr
      simpa only [pathEnd, BalancedCriticalSpectrum.flip_flip] using
        (mem_directions C _ _).mp (mem_twoStepPaths.mp p.property).1
    · apply (mem_directions C _ _).mpr
      simpa only [pathEnd, BalancedCriticalSpectrum.flip_flip] using x.property.1⟩

@[simp] private theorem pathEnd_reverse (x : Side C b) (p : PathAt C x.val) :
    pathEnd (pathEnd x p) (reversePath x p) = x := by
  apply Subtype.ext
  change bitFlip (bitFlip (bitFlip (bitFlip x.val p.val.1) p.val.2) p.val.2) p.val.1 = x.val
  simp only [BalancedCriticalSpectrum.flip_flip]

variable {a : Side C b → Exponent}

def pathExponent (a : Side C b → Exponent) (x : Side C b) (p : PathAt C x.val) :
    Exponent := a (pathEnd x p) - a x + axis p.val.1 + axis p.val.2

/-- One exponent per directed path, with multiplicity retained under the map. -/
def pathExponents (a : Side C b → Exponent) (x : Side C b) : Multiset Exponent :=
  (twoStepPaths C x.val).attach.val.map (pathExponent a x)

def missingExponents (C : Finset (Q 9)) (x : Q 9) : Multiset Exponent :=
  (exteriorDirections C x).val.map squareExponent

def monomialSum (s : Multiset Exponent) : AddMonoidAlgebra ℕ Exponent :=
  AddMonoidAlgebra.ofCoeff (Multiset.toFinsupp s)

/-- The exact positive Laurent identity in every row of the chosen side. -/
def LaurentIdentity (a : Side C b → Exponent) : Prop :=
  ∀ x, monomialSum (pathExponents a x) = monomialSum (missingExponents C x.val)

private theorem exponents_eq (h : LaurentIdentity a) (x : Side C b) :
    pathExponents a x = missingExponents C x.val := by
  apply Multiset.toFinsupp.injective
  exact congrArg AddMonoidAlgebra.coeff (h x)

/-- Equality at every positive weight vector determines the Laurent row identity. -/
theorem laurentIdentity_iff_evaluateLaurent (a : Side C b → Exponent) :
    LaurentIdentity a ↔ ∀ (x : Side C b) (w : Fin 9 → ℝ), (∀ i, 0 < w i) →
      evaluateLaurent w (pathExponents a x) = evaluateLaurent w (missingExponents C x.val) := by
  constructor
  · intro h x w _
    exact congrArg (evaluateLaurent w) (exponents_eq h x)
  · intro h x
    exact congrArg monomialSum (eq_of_evaluation_eq (h x))

private theorem squareExponent_injective : Function.Injective squareExponent := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp [squareExponent, axis, hij] at hi

private theorem exponent_matches_missing (h : LaurentIdentity a) (x : Side C b)
    (p : PathAt C x.val) :
    ∃ k ∈ exteriorDirections C x.val, pathExponent a x p = squareExponent k := by
  have hp : pathExponent a x p ∈ pathExponents a x := by
    exact Multiset.mem_map.mpr ⟨p, Finset.mem_attach _ p, rfl⟩
  rw [exponents_eq h x] at hp
  change pathExponent a x p ∈ (exteriorDirections C x.val).val.map squareExponent at hp
  obtain ⟨k, hk, he⟩ := Multiset.mem_map.mp hp
  exact ⟨k, hk, he.symm⟩

/-- A path's square exponent is on its second axis. Reversing the path cancels
the potential difference, and the first axis is internal at the starting vertex. -/
theorem path_exponent_and_gain (h : LaurentIdentity a) (x : Side C b) (p : PathAt C x.val) :
    p.val.2 ∈ exteriorDirections C x.val ∧
      pathExponent a x p = squareExponent p.val.2 ∧
      a (pathEnd x p) - a x = axis p.val.2 - axis p.val.1 := by
  obtain ⟨k, hk, hf⟩ := exponent_matches_missing h x p
  obtain ⟨l, _, hr⟩ := exponent_matches_missing h (pathEnd x p) (reversePath x p)
  have hki : k ≠ p.val.1 := by
    intro he
    apply (Finset.mem_sdiff.mp hk).2
    rw [he]
    exact (mem_twoStepPaths.mp p.property).1
  change a (pathEnd (pathEnd x p) (reversePath x p)) - a (pathEnd x p) +
    axis p.val.2 + axis p.val.1 = squareExponent l at hr
  rw [pathEnd_reverse] at hr
  have hkj : k = p.val.2 := by
    by_contra hne
    have hfk := congrFun hf k
    have hrk := congrFun hr k
    have hkf : a (pathEnd x p) k - a x k = 2 := by
      simpa [pathExponent, squareExponent, axis, hki, hne] using hfk
    by_cases hkl : k = l
    · subst l
      have hkr : a x k - a (pathEnd x p) k = 2 := by
        simpa [squareExponent, axis, hki, hne] using hrk
      omega
    · have hkr : a x k - a (pathEnd x p) k = 0 := by
        simpa [squareExponent, axis, hki, hne, hkl] using hrk
      omega
  rw [hkj] at hk hf
  refine ⟨hk, hf, ?_⟩
  funext r
  have he := congrFun hf r
  simp only [pathExponent, squareExponent, Pi.add_apply, Pi.sub_apply] at he ⊢
  omega

private theorem missing_axis_eq_second (h : LaurentIdentity a) (x : Side C b) (p : PathAt C x.val)
    {k : Fin 9} (he : pathExponent a x p = squareExponent k) : k = p.val.2 :=
  squareExponent_injective (he.symm.trans (path_exponent_and_gain h x p).2.1)

/-- Each missing axis is the second axis of exactly one directed path from `x`. -/
private theorem unique_path_for_missing (h : LaurentIdentity a) (x : Side C b) {j : Fin 9}
    (hj : j ∈ exteriorDirections C x.val) : ∃! p : PathAt C x.val, p.val.2 = j := by
  have hm : squareExponent j ∈ missingExponents C x.val :=
    Multiset.mem_map.mpr ⟨j, hj, rfl⟩
  rw [← exponents_eq h x] at hm
  change squareExponent j ∈ (twoStepPaths C x.val).attach.val.map (pathExponent a x) at hm
  obtain ⟨p, _, hp⟩ := Multiset.mem_map.mp hm
  refine ⟨p, (missing_axis_eq_second h x p hp).symm, ?_⟩
  intro q hq
  have hn : (pathExponents a x).Nodup := by
    rw [exponents_eq h x]
    exact Multiset.Nodup.map squareExponent_injective (exteriorDirections C x.val).nodup
  have he : pathExponent a x q = pathExponent a x p := by
    rw [(path_exponent_and_gain h x q).2.1, hq, hp]
  exact Multiset.inj_on_of_nodup_map
    (f := pathExponent a x) (s := (twoStepPaths C x.val).attach.val) hn
    q (Finset.mem_attach _ q) p (Finset.mem_attach _ p) he

open scoped Classical in
/-- The neighbors indexed by the three internal axes at `x` have three directions
each. Every axis belongs to exactly one of those triples. -/
theorem neighbor_triples_partition
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) (x : Side C b) :
    (directions C x.val).card = 3 ∧
      (∀ i ∈ directions C x.val, (directions C (bitFlip x.val i)).card = 3) ∧
      (∀ k : Fin 9, ∃! i : {i // i ∈ directions C x.val},
        k ∈ directions C (bitFlip x.val i.val)) := by
  refine ⟨regular_directions C hC x.property.1, ?_, ?_⟩
  · intro i hi
    exact regular_directions C hC ((mem_directions C _ _).mp hi)
  · intro k
    let path (i : {i // i ∈ directions C x.val})
        (hi : k ∈ directions C (bitFlip x.val i.val)) (hne : i.val ≠ k) : PathAt C x.val :=
      ⟨(i.val, k), mem_twoStepPaths.mpr ⟨i.property, hi, hne⟩⟩
    by_cases hk : k ∈ directions C x.val
    · have hback : k ∈ directions C (bitFlip x.val k) :=
        (mem_directions C _ _).mpr (by
          simpa only [BalancedCriticalSpectrum.flip_flip] using x.property.1)
      refine ⟨⟨k, hk⟩, hback, ?_⟩
      intro i hi
      apply Subtype.ext
      change i.val = k
      by_contra hne
      have hm := (path_exponent_and_gain h x (path i hi hne)).1
      exact (Finset.mem_sdiff.mp hm).2 hk
    · have hm : k ∈ exteriorDirections C x.val :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩
      obtain ⟨p, hp, huniq⟩ := unique_path_for_missing h x hm
      have hp' := mem_twoStepPaths.mp p.property
      refine ⟨⟨p.val.1, hp'.1⟩, ?_, ?_⟩
      · change k ∈ directions C (bitFlip x.val p.val.1)
        rw [← hp]
        exact hp'.2.1
      · intro i hi
        have hne : i.val ≠ k := by
          intro he
          apply hk
          rw [← he]
          exact i.property
        apply Subtype.ext
        exact congrArg (fun q : PathAt C x.val => q.val.1) (huniq (path i hi hne) rfl)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition
