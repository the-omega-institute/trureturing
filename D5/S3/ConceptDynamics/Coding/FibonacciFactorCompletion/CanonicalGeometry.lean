/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/CanonicalGeometry
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/CanonicalGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal literal returns determine canonical hulls and endpoint certificates. -/

import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter Topology
open scoped Topology
set_option maxHeartbeats 1000000

private theorem zero_inside_guard (s : Guard) : -1 < (0 : ℝ) ∧ 0 < supportUpper s := by
  rcases tail_arithmetic with ⟨_,ht,_,_,_,hphi⟩
  constructor
  · norm_num
  · cases s <;> simp only [supportUpper] <;> linarith

/-- Existing closed support and nonzero affine slope give strict support. -/
private theorem legal_compose_inside (s e : Guard) (w : List Label)
    (hw : LegalWord s e w) (x : ℝ) (hx : -1 < x ∧ x < supportUpper e) :
    -1 < compose w x ∧ compose w x < supportUpper s := by
  have hends : (-1 : ℝ) ≤ supportUpper e := by
    have h := zero_inside_guard e
    linarith
  exact compose_strict_inside w (-1) (supportUpper e) x (-1) (supportUpper s)
    hx.1 hx.2
    (literal_source_geometry.1 s e w (-1) hw ⟨le_rfl,hends⟩)
    (literal_source_geometry.1 s e w (supportUpper e) hw ⟨hends,le_rfl⟩)

/-- Actual root branches from one guard have disjoint interior images.
Closed branch endpoints are allowed to touch; strict tail inputs cannot hit them. -/
private theorem interior_branch_label_unique
    (s e f : Guard) (l m : Label) (x y : ℝ)
    (hl : nextGuard s l = some e) (hm : nextGuard s m = some f)
    (hx : -1 < x ∧ x < supportUpper e)
    (hy : -1 < y ∧ y < supportUpper f)
    (hvalue : branch l x = branch m y) : l = m := by
  rcases tail_arithmetic with ⟨htq,htp,ht1,hgp,hg1,hphi⟩
  have hxlo : 0 < g*(x+1) := mul_pos hgp (by linarith [hx.1])
  have hxhi : 0 < g*(supportUpper e-x) := mul_pos hgp (by linarith [hx.2])
  have hylo : 0 < g*(y+1) := mul_pos hgp (by linarith [hy.1])
  have hyhi : 0 < g*(supportUpper f-y) := mul_pos hgp (by linarith [hy.2])
  cases s <;> cases e <;> cases f <;> cases l <;> cases m <;>
    simp_all [nextGuard,supportUpper,branch,shift,phi,T2,g] <;> nlinarith

/-- Finite zero tails provide the actual equal-length legal-word injection needed
by original 39.2.2. No distinct-affine-map hypothesis is inserted. -/
private theorem legal_equal_length_zero_injective
    (s e f : Guard) (u v : List Label) (hlen : u.length = v.length)
    (hu : LegalWord s e u) (hv : LegalWord s f v)
    (hvalue : compose u 0 = compose v 0) : u = v := by
  induction u generalizing s e f v with
  | nil =>
    cases v with
    | nil => rfl
    | cons m v => simp at hlen
  | cons l u ih =>
    cases v with
    | nil => simp at hlen
    | cons m v =>
      have hlen' : u.length = v.length := by simpa using hlen
      cases hl : nextGuard s l with
      | none => simp [LegalWord,walk,hl] at hu
      | some q =>
        have hu' : LegalWord q e u := by simpa [LegalWord,walk,hl] using hu
        cases hm : nextGuard s m with
        | none => simp [LegalWord,walk,hm] at hv
        | some r =>
          have hv' : LegalWord r f v := by simpa [LegalWord,walk,hm] using hv
          have hlabels : l = m := interior_branch_label_unique s q r l m
            (compose u 0) (compose v 0) hl hm
            (legal_compose_inside q e u hu' 0 (zero_inside_guard e))
            (legal_compose_inside r f v hv' 0 (zero_inside_guard f)) hvalue
          subst m
          have hqr : q = r := Option.some.inj (hl.symm.trans hm)
          subst r
          have hgp : 0 < g := tail_arithmetic.2.2.2.1
          have htail : compose u 0 = compose v 0 := by
            change shift l-g*compose u 0 = shift l-g*compose v 0 at hvalue
            apply mul_left_cancel₀ (ne_of_gt hgp)
            linarith
          exact congrArg (List.cons l) (ih q e f v hlen' hu' hv' htail)

/-- The literal signed slope, retaining odd as well as even return lengths. -/
theorem return_slope_control (L : ℕ) (hL : 0 < L) :
    -1 < (-g)^L ∧ (-g)^L < 1 ∧ (-g)^L ≠ 0 := by
  have hgp : 0 < g := tail_arithmetic.2.2.2.1
  have hg1 : g < 1 := tail_arithmetic.2.2.2.2.1
  have hsmall : |(-g)^L| < 1 := by
    rw [abs_pow,abs_neg,abs_of_pos hgp]
    exact pow_lt_one₀ hgp.le hg1 (by omega)
  exact ⟨(abs_lt.mp hsmall).1,(abs_lt.mp hsmall).2,
    pow_ne_zero _ (neg_ne_zero.mpr (ne_of_gt hgp))⟩

/-- Exact source formulas for both signs; A is the actual pair of translations. -/
noncomputable def canonicalAffineLo (A : Bool → ℝ) (a : ℝ) : ℝ :=
  if 0 < a then min (A false) (A true)/(1-a)
  else (min (A false) (A true)+a*max (A false) (A true))/(1-a^2)

noncomputable def canonicalAffineHi (A : Bool → ℝ) (a : ℝ) : ℝ :=
  if 0 < a then max (A false) (A true)/(1-a)
  else (max (A false) (A true)+a*min (A false) (A true))/(1-a^2)

/-- Endpoint contacts, signed width, invariance and minimality are all computed.
Minimality uses endpoint inequalities of the same invariant interval. -/
theorem canonical_affine_hull (A : Bool → ℝ) (a : ℝ)
    (ha : -1 < a) (ha1 : a < 1) :
    let lo := canonicalAffineLo A a
    let hi := canonicalAffineHi A a
    lo ≤ hi ∧
    (A false ≠ A true → lo < hi) ∧
    (hi-lo = (max (A false) (A true)-min (A false) (A true)) /
      (if 0 < a then 1-a else 1+a)) ∧
    (if 0 < a then
      lo = min (A false) (A true)+a*lo ∧ hi = max (A false) (A true)+a*hi
     else
      lo = min (A false) (A true)+a*hi ∧ hi = max (A false) (A true)+a*lo) ∧
    (∀ i z, lo ≤ z → z ≤ hi → lo ≤ A i+a*z ∧ A i+a*z ≤ hi) ∧
    (∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ A i+a*z ∧ A i+a*z ≤ u) →
      l ≤ lo ∧ hi ≤ u) := by
  let amin := min (A false) (A true)
  let amax := max (A false) (A true)
  let lo := canonicalAffineLo A a
  let hi := canonicalAffineHi A a
  have minuspos : 0 < 1-a := by linarith
  have pluspos : 0 < 1+a := by linarith
  have squarepos : 0 < 1-a^2 := by nlinarith [mul_pos minuspos pluspos]
  have delta : 0 ≤ amax-amin := sub_nonneg.mpr min_le_max
  have bounds : ∀ i, amin ≤ A i ∧ A i ≤ amax := by
    intro i
    cases i
    · exact ⟨min_le_left _ _,le_max_left _ _⟩
    · exact ⟨min_le_right _ _,le_max_right _ _⟩
  obtain ⟨imin,imax,hmin,hmax⟩ :
      ∃ imin imax : Bool, A imin = amin ∧ A imax = amax := by
    by_cases h : A false ≤ A true
    · exact ⟨false,true,(min_eq_left h).symm,(max_eq_right h).symm⟩
    · exact ⟨true,false,(min_eq_right (le_of_not_ge h)).symm,
        (max_eq_left (le_of_not_ge h)).symm⟩
  have width : hi-lo = (amax-amin)/(if 0 < a then 1-a else 1+a) := by
    by_cases apos : 0 < a
    · simp only [lo,hi,canonicalAffineLo,canonicalAffineHi,if_pos apos]
      dsimp [amin,amax]
      ring
    · simp only [lo,hi,canonicalAffineLo,canonicalAffineHi,if_neg apos]
      dsimp [amin,amax]
      field_simp [ne_of_gt squarepos,ne_of_gt pluspos]
      ring
  have denompos : 0 < (if 0 < a then 1-a else 1+a) := by
    split_ifs <;> assumption
  have ordered : lo ≤ hi := by
    have hd : 0 ≤ hi-lo := by rw [width]; exact div_nonneg delta denompos.le
    linarith
  have strict : A false ≠ A true → lo < hi := by
    intro hne
    have dp : 0 < amax-amin := by
      rcases lt_or_gt_of_ne hne with h | h
      · dsimp [amin,amax]
        rw [min_eq_left h.le,max_eq_right h.le]
        linarith
      · dsimp [amin,amax]
        rw [min_eq_right h.le,max_eq_left h.le]
        linarith
    have hd : 0 < hi-lo := by rw [width]; exact div_pos dp denompos
    linarith
  have contact : if 0 < a then lo=amin+a*lo ∧ hi=amax+a*hi
      else lo=amin+a*hi ∧ hi=amax+a*lo := by
    by_cases apos : 0 < a
    · simp only [lo,hi,canonicalAffineLo,canonicalAffineHi,if_pos apos]
      dsimp [amin,amax]
      constructor <;> field_simp [ne_of_gt minuspos] <;> ring
    · simp only [lo,hi,canonicalAffineLo,canonicalAffineHi,if_neg apos]
      dsimp [amin,amax]
      constructor <;> field_simp [ne_of_gt squarepos] <;> ring
  have invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ A i+a*z ∧ A i+a*z ≤ hi := by
    intro i z hzlo hzhi
    by_cases apos : 0 < a
    · have heq := contact
      rw [if_pos apos] at heq
      constructor
      · calc lo = amin+a*lo := heq.1
             _ ≤ A i+a*z := add_le_add (bounds i).1 (mul_le_mul_of_nonneg_left hzlo apos.le)
      · calc A i+a*z ≤ amax+a*hi := add_le_add (bounds i).2 (mul_le_mul_of_nonneg_left hzhi apos.le)
             _ = hi := heq.2.symm
    · have ale : a ≤ 0 := le_of_not_gt apos
      have heq := contact
      rw [if_neg apos] at heq
      constructor
      · calc lo = amin+a*hi := heq.1
             _ ≤ A i+a*z := add_le_add (bounds i).1 (mul_le_mul_of_nonpos_left hzhi ale)
      · calc A i+a*z ≤ amax+a*lo := add_le_add (bounds i).2 (mul_le_mul_of_nonpos_left hzlo ale)
             _ = hi := heq.2.symm
  have minimal : ∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ A i+a*z ∧ A i+a*z ≤ u) →
      l ≤ lo ∧ hi ≤ u := by
    intro l u hlu hinv
    by_cases apos : 0 < a
    · have low := (hinv imin l le_rfl hlu).1
      have high := (hinv imax u hlu le_rfl).2
      rw [hmin] at low
      rw [hmax] at high
      change l ≤ canonicalAffineLo A a ∧ canonicalAffineHi A a ≤ u
      simp only [canonicalAffineLo,canonicalAffineHi,if_pos apos]
      constructor
      · apply (le_div_iff₀ minuspos).mpr
        change l*(1-a) ≤ amin
        nlinarith [low]
      · apply (div_le_iff₀ minuspos).mpr
        change amax ≤ u*(1-a)
        nlinarith [high]
    · have ale : a ≤ 0 := le_of_not_gt apos
      have low := (hinv imin u hlu le_rfl).1
      have high := (hinv imax l le_rfl hlu).2
      rw [hmin] at low
      rw [hmax] at high
      have lowerTwo : l ≤ amin+a*(amax+a*l) :=
        low.trans (add_le_add le_rfl (mul_le_mul_of_nonpos_left high ale))
      have upperTwo : amax+a*(amin+a*u) ≤ u :=
        (add_le_add le_rfl (mul_le_mul_of_nonpos_left low ale)).trans high
      change l ≤ canonicalAffineLo A a ∧ canonicalAffineHi A a ≤ u
      simp only [canonicalAffineLo,canonicalAffineHi,if_neg apos]
      constructor
      · apply (le_div_iff₀ squarepos).mpr
        change l*(1-a^2) ≤ amin+a*amax
        nlinarith [lowerTwo]
      · apply (div_le_iff₀ squarepos).mpr
        change amax+a*amin ≤ u*(1-a^2)
        nlinarith [upperTwo]
  exact ⟨ordered,strict,width,contact,invariant,minimal⟩

noncomputable def canonicalReturnLo (U : Bool → List Label) (L : ℕ) : ℝ :=
  canonicalAffineLo (fun i => compose (U i) 0) ((-g)^L)

noncomputable def canonicalReturnHi (U : Bool → List Label) (L : ℕ) : ℝ :=
  canonicalAffineHi (fun i => compose (U i) 0) ((-g)^L)

/-- The coefficient field Q(t), defined as the intersection of all real
subfields containing the literal Fibonacci coefficient t. -/
def coefficientField : Subfield ℝ where
  carrier := {x | ∀ F : Subfield ℝ, t ∈ F → x ∈ F}
  zero_mem' := fun F _ => F.zero_mem
  one_mem' := fun F _ => F.one_mem
  add_mem' := fun hx hy F ht => F.add_mem (hx F ht) (hy F ht)
  neg_mem' := fun hx F ht => F.neg_mem (hx F ht)
  mul_mem' := fun hx hy F ht => F.mul_mem (hx F ht) (hy F ht)
  inv_mem' := fun x hx F ht => F.inv_mem (hx F ht)

theorem literal_coefficient_mem (w : List Label) : compose w 0 ∈ coefficientField := by
  have tmem : t ∈ coefficientField := fun F ht => ht
  have gmem : g ∈ coefficientField := by
    dsimp only [g]
    exact coefficientField.sub_mem
      (coefficientField.mul_mem (by simpa using coefficientField.intCast_mem (2 : ℤ)) tmem)
      coefficientField.one_mem
  have labelmem (l : Label) : shift l ∈ coefficientField := by
    cases l
    · exact coefficientField.neg_mem tmem
    · exact coefficientField.zero_mem
    · exact coefficientField.sub_mem coefficientField.one_mem tmem
    · exact coefficientField.one_mem
    · exact coefficientField.sub_mem
        (by simpa using coefficientField.intCast_mem (2 : ℤ)) tmem
  induction w with
  | nil => exact coefficientField.zero_mem
  | cons l w ih => exact coefficientField.sub_mem (labelmem l) (coefficientField.mul_mem gmem ih)

theorem canonical_return_coefficient_mem (U : Bool → List Label) (L : ℕ) :
    canonicalReturnLo U L ∈ coefficientField ∧ canonicalReturnHi U L ∈ coefficientField := by
  have tmem : t ∈ coefficientField := fun F ht => ht
  have gmem : g ∈ coefficientField := by
    dsimp only [g]
    exact coefficientField.sub_mem
      (coefficientField.mul_mem (by simpa using coefficientField.intCast_mem (2 : ℤ)) tmem)
      coefficientField.one_mem
  have amem := coefficientField.pow_mem (coefficientField.neg_mem gmem) L
  have minmem : min (compose (U false) 0) (compose (U true) 0) ∈ coefficientField := by
    rcases le_total (compose (U false) 0) (compose (U true) 0) with h | h
    · rw [min_eq_left h]; exact literal_coefficient_mem _
    · rw [min_eq_right h]; exact literal_coefficient_mem _
  have maxmem : max (compose (U false) 0) (compose (U true) 0) ∈ coefficientField := by
    rcases le_total (compose (U false) 0) (compose (U true) 0) with h | h
    · rw [max_eq_right h]; exact literal_coefficient_mem _
    · rw [max_eq_left h]; exact literal_coefficient_mem _
  dsimp only [canonicalReturnLo, canonicalReturnHi, canonicalAffineLo, canonicalAffineHi]
  split_ifs
  · exact ⟨coefficientField.div_mem minmem (coefficientField.sub_mem coefficientField.one_mem amem),
      coefficientField.div_mem maxmem (coefficientField.sub_mem coefficientField.one_mem amem)⟩
  · exact ⟨coefficientField.div_mem (coefficientField.add_mem minmem (coefficientField.mul_mem amem maxmem))
        (coefficientField.sub_mem coefficientField.one_mem (coefficientField.pow_mem amem 2)),
      coefficientField.div_mem (coefficientField.add_mem maxmem (coefficientField.mul_mem amem minmem))
        (coefficientField.sub_mem coefficientField.one_mem (coefficientField.pow_mem amem 2))⟩

/-- Canonical support and minimality come from actual legal returns; strict width
comes from their literal difference, not a separately supplied geometric premise. -/
theorem canonical_legal_return_hull (s : Guard) (U : Bool → List Label)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length=L)
    (hlegal : ∀ i, LegalWord s s (U i)) :
    let lo := canonicalReturnLo U L
    let hi := canonicalReturnHi U L
    lo ≤ hi ∧
    (U false ≠ U true → lo < hi) ∧
    (∀ z ∈ Set.Icc lo hi, InSupport s z) ∧
    (∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (U i) z ∧ compose (U i) z ≤ hi) ∧
    (∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ compose (U i) z ∧ compose (U i) z ≤ u) →
      l ≤ lo ∧ hi ≤ u) ∧
    (lo = hi ↔ U false = U true) ∧
    (lo ∈ coefficientField ∧ hi ∈ coefficientField) := by
  let A : Bool → ℝ := fun i => compose (U i) 0
  let a : ℝ := (-g)^L
  have slope := return_slope_control L hL
  have affine (i : Bool) (z : ℝ) : compose (U i) z = A i+a*z := by
    simpa only [zero_add,hlen] using literal_source_geometry.2.2.2.1 (U i) 0 z
  obtain ⟨ordered,strict,width,contact,invariant,minimal⟩ :=
    canonical_affine_hull A a slope.1 slope.2.1
  have realInvariant : ∀ i z, canonicalReturnLo U L ≤ z → z ≤ canonicalReturnHi U L →
      canonicalReturnLo U L ≤ compose (U i) z ∧ compose (U i) z ≤ canonicalReturnHi U L := by
    intro i z hzlo hzhi
    rw [affine]
    exact invariant i z hzlo hzhi
  have realMinimal : ∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ compose (U i) z ∧ compose (U i) z ≤ u) →
      l ≤ canonicalReturnLo U L ∧ canonicalReturnHi U L ≤ u := by
    intro l u hlu h
    apply minimal l u hlu
    intro i z hzlo hzhi
    simpa only [affine] using h i z hzlo hzhi
  have guardOrdered : (-1 : ℝ) ≤ supportUpper s := by
    have h := zero_inside_guard s
    linarith
  have endpoints := realMinimal (-1) (supportUpper s) guardOrdered
    (fun i z hzlo hzhi => literal_source_geometry.1 s s (U i) z (hlegal i) ⟨hzlo,hzhi⟩)
  have singleton : canonicalReturnLo U L = canonicalReturnHi U L ↔ U false = U true := by
    constructor
    · intro heq
      by_contra hne
      have hs : canonicalReturnLo U L < canonicalReturnHi U L := strict (fun hz =>
        hne (legal_equal_length_zero_injective s s s (U false) (U true)
          ((hlen false).trans (hlen true).symm) (hlegal false) (hlegal true) hz))
      rw [heq] at hs
      exact (lt_irrefl _ hs)
    · intro heq
      simp only [canonicalReturnLo, canonicalReturnHi, canonicalAffineLo, canonicalAffineHi,
        heq, min_self, max_self]
  refine ⟨ordered,?_,?_,realInvariant,realMinimal,singleton,canonical_return_coefficient_mem U L⟩
  · intro hne
    apply strict
    intro heq
    exact hne (legal_equal_length_zero_injective s s s (U false) (U true)
      ((hlen false).trans (hlen true).symm) (hlegal false) (hlegal true) heq)
  · intro z hz
    exact ⟨endpoints.1.trans hz.1,hz.2.trans endpoints.2⟩

noncomputable def endpointCosts (lo hi : ℝ) (w : List Label) (cs : List Color) : List ℝ :=
  List.ofFn (fun r : Fin cs.length =>
    max (max (cut cs[r].val-compose (w.drop r.val) lo)
      (max 0 (compose (w.drop r.val) lo-cut (cs[r].val+1))))
      (max (cut cs[r].val-compose (w.drop r.val) hi)
        (max 0 (compose (w.drop r.val) hi-cut (cs[r].val+1)))))

/-- Every observed stem and return suffix is retained, on both actual sources. -/
noncomputable def familyEndpointCosts (P Q : List Label) (h : List Color)
    (U V : Bool → List Label) (W : Bool → List Color) (L : ℕ) : List ℝ :=
  endpointCosts (canonicalReturnLo U L) (canonicalReturnHi U L) P h ++
  endpointCosts (canonicalReturnLo V L) (canonicalReturnHi V L) Q h ++
  endpointCosts (canonicalReturnLo U L) (canonicalReturnHi U L) (U false) (W false) ++
  endpointCosts (canonicalReturnLo U L) (canonicalReturnHi U L) (U true) (W true) ++
  endpointCosts (canonicalReturnLo V L) (canonicalReturnHi V L) (V false) (W false) ++
  endpointCosts (canonicalReturnLo V L) (canonicalReturnHi V L) (V true) (W true)

noncomputable def familyEndpointBudget (P Q : List Label) (h : List Color)
    (U V : Bool → List Label) (W : Bool → List Color) (L : ℕ) : ℝ :=
  (familyEndpointCosts P Q h U V W L).foldr max 0

private theorem max_fold_nonnegative (xs : List ℝ) : 0 ≤ xs.foldr max 0 := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)

private theorem endpoint_certificate_of_budget (s e : Guard) (w : List Label)
    (cs : List Color) (lo hi : ℝ) (hw : LegalWord s e w)
    (hlo : InSupport e lo) (hhi : InSupport e hi) (costs : List ℝ)
    (part : ∀ c ∈ endpointCosts lo hi w cs, c ∈ costs) :
    EndpointCertificate (costs.foldr max 0) lo hi w cs := by
  intro r hr
  have hm : max (max (cut cs[r].val-compose (w.drop r) lo)
      (max 0 (compose (w.drop r) lo-cut (cs[r].val+1))))
      (max (cut cs[r].val-compose (w.drop r) hi)
        (max 0 (compose (w.drop r) hi-cut (cs[r].val+1)))) ∈ endpointCosts lo hi w cs :=
    List.mem_ofFn.mpr ⟨⟨r,hr⟩,rfl⟩
  have bound := List.le_max_of_le' 0 (part _ hm) le_rfl
  exact ⟨⟨suffix_supported s e w hw lo hlo r,(le_max_left _ _).trans bound⟩,
    ⟨suffix_supported s e w hw hi hhi r,(le_max_right _ _).trans bound⟩⟩

/-- The original finite endpoint maximum supplies the canonical high tail.
Certificates for all six indexed groups are derived from that same maximum. -/
theorem endpoint_certificate_mono (a b lo hi : ℝ) (w : List Label) (cs : List Color)
    (hab : a ≤ b) (cert : EndpointCertificate a lo hi w cs) :
    EndpointCertificate b lo hi w cs := by
  intro r hr
  obtain ⟨⟨hslo,hblo⟩,⟨hshi,hbhi⟩⟩ := cert r hr
  exact ⟨⟨hslo,hblo.trans hab⟩,⟨hshi,hbhi.trans hab⟩⟩

theorem family_endpoint_certificates
    (o : Ownership) (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L)
    (hlegal : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (hcolors : ∀ i, (U i).length = (W i).length) :
    let θ := familyEndpointBudget P Q h U V W L
    0 ≤ θ ∧ (familyEndpointCosts P Q h U V W L).length = 2*h.length+4*L ∧
    EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L) P h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L) (U i) (W i)) ∧
    EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) Q h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) (V i) (W i)) := by
  let costs := familyEndpointCosts P Q h U V W L
  let θ := familyEndpointBudget P Q h U V W L
  have highHull := canonical_legal_return_hull s1 U L hL hlen hlegal
  have lowHull := canonical_legal_return_hull s2 V L hL hVlen hV
  have highLo := highHull.2.2.1 (canonicalReturnLo U L) ⟨le_rfl,highHull.1⟩
  have highHi := highHull.2.2.1 (canonicalReturnHi U L) ⟨highHull.1,le_rfl⟩
  have lowLo := lowHull.2.2.1 (canonicalReturnLo V L) ⟨le_rfl,lowHull.1⟩
  have lowHi := lowHull.2.2.1 (canonicalReturnHi V L) ⟨lowHull.1,le_rfl⟩
  have highStem : EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L) P h := by
    apply endpoint_certificate_of_budget .G0 s1 P h _ _ hP highLo highHi costs
    intro c hc
    simp only [costs,familyEndpointCosts,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc))))
  have lowStem : EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) Q h := by
    apply endpoint_certificate_of_budget .G0 s2 Q h _ _ hQ lowLo lowHi costs
    intro c hc
    simp only [costs,familyEndpointCosts,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))
  have highReturns : ∀ i, EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L)
      (U i) (W i) := by
    intro i
    apply endpoint_certificate_of_budget s1 s1 (U i) (W i) _ _ (hlegal i) highLo highHi costs
    intro c hc
    simp only [costs,familyEndpointCosts,List.mem_append]
    cases i
    · exact Or.inl (Or.inl (Or.inl (Or.inr hc)))
    · exact Or.inl (Or.inl (Or.inr hc))
  have lowReturns : ∀ i, EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L)
      (V i) (W i) := by
    intro i
    apply endpoint_certificate_of_budget s2 s2 (V i) (W i) _ _ (hV i) lowLo lowHi costs
    intro c hc
    simp only [costs,familyEndpointCosts,List.mem_append]
    cases i
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  have hθ : 0 ≤ θ := max_fold_nonnegative costs
  have wlen : ∀ i, (W i).length = L := fun i => (hcolors i).symm.trans (hlen i)
  have count : costs.length = 2*h.length+4*L := by
    simp only [costs,familyEndpointCosts,endpointCosts,List.length_append,List.length_ofFn,wlen]
    omega
  exact ⟨hθ,count,highStem,highReturns,lowStem,lowReturns⟩


end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
