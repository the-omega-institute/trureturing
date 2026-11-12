/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete effective and cardinal bounds for actual integral tail candidates. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairTailSpectrum
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Source: the full fixed-pair quadratic/harmonic/unique-tail reductions,
PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The finite
candidate sets contain actual algebraic roots at every allowed offset,
not selected samples. Membership is necessary, never sufficient, for
integral spectrum. The repeated exponent and first tail remain unbounded. -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.PairTailCandidates
open PairTailArithmetic IdealIntersectionSupport IdealIntersectionObstructions
open PairedIdealIntersectionLift

def positiveTails (a b t : ℤ) : Finset ℤ :=
  (tailPolynomial a b t).roots.toFinset.filter (0<·)

def candidates (a b : ℕ) : Finset ℤ :=
  (Ioo (0:ℤ) (((a:ℤ)+1)*b)).biUnion (positiveTails (a:ℤ) (b:ℤ))

def harmonicCandidates (a b : ℕ) : Finset ℤ :=
  (Ioo (b:ℤ) (2*b)).biUnion (positiveTails (a:ℤ) (b:ℤ))

theorem positiveTails_card (a b t : ℤ) : (positiveTails a b t).card≤2 := by
  exact (Finset.card_filter_le _ _).trans
    (((tailPolynomial a b t).roots.toFinset_card_le).trans ((Polynomial.card_roots' _).trans (degree_le_two a b t)))

theorem harmonic_fiber_card (a b t : ℤ) (ha : 1≤a) (hl : b<t) (hu : t<2*b) :
    (positiveTails a b t).card≤1 := by
  apply Finset.card_le_one.mpr
  intro c hc d hd
  have hc':=(Finset.mem_filter.mp hc)
  have hd':=(Finset.mem_filter.mp hd)
  have hcz : (tailPolynomial a b t).eval c=0 :=
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hc'.1)
  have hdz : (tailPolynomial a b t).eval d=0 :=
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hd'.1)
  rw [eval_tailPolynomial] at hcz hdz
  exact positive_root_unique a b t c d ha hl hu hc'.2 hd'.2 hcz hdz

/-- At most two roots at every one of the d-1 offsets. -/
theorem candidate_card (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    (candidates a b).card≤2*((a+1)*b-1) := by
  have hi : (Ioo (0:ℤ) (((a:ℤ)+1)*b)).card=(a+1)*b-1 := by
    rw [Int.card_Ioo]
    have heq : ((a:ℤ)+1)*b = (((a+1)*b:ℕ):ℤ) := by push_cast; rfl
    rw [heq]
    omega
  have hh:=Finset.card_biUnion_le_card_mul
    (Ioo (0:ℤ) (((a:ℤ)+1)*b)) (positiveTails (a:ℤ) (b:ℤ)) 2
    (fun t _ => positiveTails_card _ _ t)
  simpa [candidates,hi,Nat.mul_comm] using hh

/-- At most one positive root at every one of the b-1 harmonic offsets. -/
theorem harmonic_card (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    (harmonicCandidates a b).card≤b-1 := by
  have hi : (Ioo (b:ℤ) (2*b)).card=b-1 := by
    rw [Int.card_Ioo]
    omega
  have hh:=Finset.card_biUnion_le_card_mul
    (Ioo (b:ℤ) (2*b)) (positiveTails (a:ℤ) (b:ℤ)) 1 (by
      intro t ht
      obtain ⟨hl,hu⟩:=Finset.mem_Ioo.mp ht
      exact harmonic_fiber_card _ _ t (by exact_mod_cast (show 1≤a by omega)) hl hu)
  simpa [harmonicCandidates,hi] using hh

private theorem mem_positiveTails (a b t c : ℤ) (ha : 0<a) (hb : 0<b)
    (ht : 0<t) (hu : t<(a+1)*b) (hc : 0<c)
    (hz : (PairedIdealIntersectionObstructions.tensorK a b c-(a+1+t) • 1).det=0) :
    c∈positiveTails a b t := by
  apply Finset.mem_filter.mpr
  refine ⟨Multiset.mem_toFinset.mpr ?_,hc⟩
  apply (Polynomial.mem_roots (polynomial_nonzero a b t ha hb ht hu)).mpr
  change (tailPolynomial a b t).eval c=0
  rw [eval_tailPolynomial]
  exact hz

/-- Every positive actual integral graph tail belongs to the complete
finite algebraic candidate set, uniformly in the four distinct primes. -/
theorem actual_mem (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    (c:ℤ)∈candidates a b := by
  obtain ⟨t,ht,hu,hz,_⟩:=PairTailSpectrum.actual_tail_candidate p hp hinj a b c ha hb hc H
  apply Finset.mem_biUnion.mpr
  exact ⟨t,Finset.mem_Ioo.mpr ⟨ht,hu⟩,
    mem_positiveTails _ _ _ _ (by positivity) (by positivity) ht hu (by positivity) hz⟩

/-- Every actual integral graph with b<c belongs to at most b-1 positive
tails; no finite restriction is imposed on a or b. -/
theorem actual_harmonic_mem (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hbc : b<c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    (c:ℤ)∈harmonicCandidates a b := by
  obtain ⟨t,hl,hu,_,hz⟩:=PairTailSpectrum.actual_harmonic_candidate p hp hinj a b c ha hb hbc H
  apply Finset.mem_biUnion.mpr
  refine ⟨t,Finset.mem_Ioo.mpr ⟨hl,hu⟩,?_⟩
  apply mem_positiveTails _ _ _ _ (by positivity) (by positivity)
    (by omega) (by nlinarith [show (1:ℤ)≤a by exact_mod_cast (show 1≤a by omega)])
    (by exact_mod_cast (show 0<c by omega)) hz

def cutoff (a b : ℤ) : ℤ :=
  let d:=(a+1)*b
  let U:=d^2/4
  U*(U+a*(d-1)+a^2*b)

/-- The full effective floor-square constant bound. -/
theorem constant_le_cutoff (a b t : ℤ) (ha : 0<a) (hb : 0<b)
    (ht : 0<t) (hu : t<(a+1)*b) : H a b t≤cutoff a b := by
  let d:=(a+1)*b
  let U:=d^2/4
  have hd : 0<d := by dsimp [d]; positivity
  have htd : t<d := hu
  have hz : 0≤t*(d-t) := by positivity
  have hm : t*(d-t)≤U := by
    dsimp [U]
    apply (Int.le_ediv_iff_mul_le (by norm_num : (0:ℤ)<4)).mpr
    nlinarith [sq_nonneg (d-2*t)]
  have hU : 0≤U := hz.trans hm
  have hr : t*(d-t)+a*t+a^2*b≤U+a*(d-1)+a^2*b := by
    have ht1 : t≤d-1 := by omega
    nlinarith
  have hp : 0≤t*(d-t)+a*t+a^2*b := by positivity
  have he:=mul_le_mul hm hr hp hU
  simpa [H,cutoff,d,U] using he

/-- Any actual integral positive tail obeys the uniform explicit cutoff.
In particular every larger tail is nonintegral, with no exponent scan. -/
theorem actual_le_cutoff (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (HI : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    (c:ℤ)≤cutoff (a:ℤ) (b:ℤ) := by
  obtain ⟨t,ht,hu,_,hdvd⟩:=PairTailSpectrum.actual_tail_candidate p hp hinj a b c ha hb hc HI
  have hH:=H_positive (a:ℤ) (b:ℤ) t (by positivity) (by positivity) ht hu
  exact (Int.le_of_dvd hH hdvd).trans (constant_le_cutoff _ _ _ (by positivity) (by positivity) ht hu)

def harmonicCutoff (a b : ℤ) : ℤ :=
  let d := (a+1)*b
  let T := 2*b-1
  let J := T*(d-T)
  J*(J+a*T+a^2*b)

/-- The full source harmonic constant bound includes its upper offset. -/
theorem constant_le_harmonic (a b t : ℤ) (ha : 3 ≤ a) (hb : 0 < b)
    (hl : b < t) (hu : t < 2*b) : H a b t ≤ harmonicCutoff a b := by
  let d := (a+1)*b
  let T := 2*b-1
  have ht0 : 0 < t := by omega
  have ha0 : 0 < a := by omega
  have htd : 0 < d-t := by dsimp [d]; nlinarith
  have htt : t ≤ T := by dsimp [T]; omega
  have hdt : 0 ≤ d-T-t := by dsimp [d,T]; nlinarith
  have hM : t*(d-t) ≤ T*(d-T) := by
    have hh := mul_nonneg (sub_nonneg.mpr htt) hdt
    nlinarith
  have hN : t*(d-t)+a*t+a^2*b ≤ T*(d-T)+a*T+a^2*b := by nlinarith
  have hz : 0 ≤ t*(d-t)+a*t+a^2*b := by positivity
  have hJ : 0 ≤ T*(d-T) := (by positivity : 0 ≤ t*(d-t)).trans hM
  have hp := mul_le_mul hM hN hz hJ
  simpa [H,harmonicCutoff,d,T] using hp

/-- All actual integral graphs with an unequal larger tail obey the
original sharpened bound when a is at least three. -/
theorem actual_le_harmonic (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 3 ≤ a) (hb : 0 < b) (hbc : b < c)
    (HI : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    (c:ℤ) ≤ harmonicCutoff (a:ℤ) (b:ℤ) := by
  obtain ⟨t,hl,hu,_,hd⟩ := PairTailSpectrum.actual_harmonic_candidate p hp hinj
    a b c (by omega) hb hbc HI
  have hH := H_positive (a:ℤ) (b:ℤ) t (by positivity) (by positivity)
    (by omega) (by nlinarith [show (3:ℤ) ≤ a by exact_mod_cast ha])
  exact (Int.le_of_dvd hH (root_divides _ _ _ _ hd)).trans
    (constant_le_harmonic _ _ _ (by exact_mod_cast ha) (by positivity) hl hu)

end D5.S3.Combinatorics.SpectralGraph.PairTailCandidates
