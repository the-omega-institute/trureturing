/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEqualitySpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportEqualitySpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real equality-curve spectral order without an endpoint-one premise. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointOneSpectrum

/-! Source: the revised endpoint-one-equality-spectrum proposition, manuscript
revision b93becea662a746badeadba42fdc3d3eb3db9382, original endpoint spectrum
blob b61e5619a508f11c7df335dd468ce61e2aa60000. The complete real domain
2<=a<=b and c=b(b+2)-a is retained without assuming h(1)=0. Instead of
interlacing the deleted block, the proof uses the derivative sign of the
actual characteristic factor and the already proved global spectral gap.
The integer-point problem on the equality curve remains distinct and open. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEqualitySpectrum
open Matrix Polynomial Finset
open D5.S3.Combinatorics.SpectralGraph
open SixSupportClassificationAlgebra SixSupportLaplacianLowRoot
open SixSupportInertia SixSupportSpectralGap

/-- Exact division of the actual quintic by its equality root b. -/
def residual (a b : ℝ) : ℝ[X] :=
  quintic a b (b*(b+2)-a) /ₘ (X-C b)

/-- The equality root b is present for every real a,b, before ordering. -/
theorem factorization (a b : ℝ) :
    (X-C b)*residual a b = quintic a b (b*(b+2)-a) := by
  apply Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
  change h a b (b*(b+2)-a) b = 0
  rw [(SixSupportEndpointOneArithmetic.exponent_value a b (b*(b+2)-a)).2.1]
  ring

private def magnitude (m t : ℝ) : ℝ :=
    2*m^9 +
    15*m^8*t +
    43*m^8 +
    49*m^7*t^2 +
    292*m^7*t +
    408*m^7 +
    91*m^6*t^3 +
    850*m^6*t^2 +
    2469*m^6*t +
    2243*m^6 +
    105*m^5*t^4 +
    1378*m^5*t^3 +
    6276*m^5*t^2 +
    11848*m^5*t +
    7876*m^5 +
    77*m^4*t^5 +
    1350*m^4*t^4 +
    8643*m^4*t^3 +
    25580*m^4*t^2 +
    35304*m^4*t +
    18324*m^4 +
    35*m^3*t^6 +
    808*m^3*t^5 +
    6913*m^3*t^4 +
    28760*m^3*t^3 +
    62186*m^3*t^2 +
    66912*m^3*t +
    28256*m^3 +
    9*m^2*t^7 +
    282*m^2*t^6 +
    3174*m^2*t^5 +
    17640*m^2*t^4 +
    53582*m^2*t^3 +
    90208*m^2*t^2 +
    78800*m^2*t +
    27856*m^2 +
    m*t^8 +
    50*m*t^7 +
    759*m*t^6 +
    5538*m*t^5 +
    22448*m*t^4 +
    53024*m*t^3 +
    72328*m*t^2 +
    52736*m*t +
    15936*m +
    3*t^8 +
    70*t^7 +
    683*t^6 +
    3624*t^5 +
    11404*t^4 +
    21784*t^3 +
    24736*t^2 +
    15360*t +
    4032

set_option maxHeartbeats 2000000 in
private theorem derivative_identity (m t : ℝ) :
    (quintic (2+m) (2+m+t) ((2+m+t)*(2+m+t+2)-(2+m))).derivative.eval (2+m+t) =
      -magnitude m t := by
  simp [quintic,magnitude,Polynomial.derivative_sub,Polynomial.derivative_add,
    Polynomial.derivative_mul,Polynomial.derivative_pow]
  ring

private theorem magnitude_positive (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) :
    0 < magnitude m t := by
  unfold magnitude
  positivity

/-- The b-root is simple throughout the complete revised real domain. -/
theorem derivative_negative (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (quintic a b (b*(b+2)-a)).derivative.eval b < 0 := by
  have hid := derivative_identity (a-2) (b-a)
  have haeq : 2+(a-2) = a := by ring
  have hbeq : a+(b-a) = b := by ring
  rw [haeq,hbeq] at hid
  rw [hid]
  exact neg_neg_of_pos (magnitude_positive (a-2) (b-a) (by linarith) (by linarith))

private theorem quotient_factor (a b : ℝ) :
    (quotient a b (b*(b+2)-a)).charpoly = X*((X-C b)*residual a b) := by
  have hq : (quotient a b (b*(b+2)-a)).charpoly = X*quintic a b (b*(b+2)-a) := by
    change (SixSupportLaplacianPolynomial.quotientOver a b (b*(b+2)-a)).charpoly = _
    rw [SixSupportLaplacianPolynomial.charpoly_zero_factor,quintic_eq_reduced]
  rw [hq,factorization]

private theorem residual_nonzero (a b : ℝ) : residual a b ≠ 0 := by
  have hq := quotient_factor a b
  intro hz
  rw [hz,mul_zero,mul_zero] at hq
  exact (quotient a b (b*(b+2)-a)).charpoly_monic.ne_zero hq

/-- The entire actual characteristic multiset retains the equality root. -/
theorem roots_relation (a b : ℝ) :
    (quotient a b (b*(b+2)-a)).charpoly.roots = {0}+{b}+(residual a b).roots := by
  rw [quotient_factor,Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero b) (residual_nonzero a b))),
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero b) (residual_nonzero a b))]
  simp [Multiset.cons_swap]

private theorem residual_at_b (a b : ℝ) :
    (residual a b).eval b = (quintic a b (b*(b+2)-a)).derivative.eval b := by
  have hd := congrArg (fun f : ℝ[X] => f.derivative.eval b) (factorization a b)
  simpa using hd

private theorem low_root (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∃ μ : ℝ, 0 < μ ∧ μ < b ∧ (residual a b).eval μ = 0 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < b*(b+2)-a := by
    nlinarith [sq_nonneg b]
  have hq0 : h a b (b*(b+2)-a) 0 < 0 := by
    have he0 (u v w : ℝ) : h u v w 0 =
        -((u+v+w)^2*(u*v*w)+(u+v+w)*(u*v+u*w+v*w)*(u*v*w)) := by
      simp [h,quintic]
    rw [he0]
    apply neg_neg_of_pos
    positivity
  have hz := congrArg (Polynomial.eval 0) (factorization a b)
  change ((X-C b)*residual a b).eval 0 = h a b (b*(b+2)-a) 0 at hz
  simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,zero_sub] at hz
  have h0 : 0 < (residual a b).eval 0 := by
    have hn : (-b)*(residual a b).eval 0 < 0 := hz.trans_lt hq0
    rcases mul_neg_iff.mp hn with h | h
    · linarith [h.1]
    · exact h.2
  have hb : (residual a b).eval b < 0 := by
    rw [residual_at_b]
    exact derivative_negative a b ha hab
  obtain ⟨μ,hμ,hzero⟩ := intermediate_value_Ioo' hb0.le
    (show ContinuousOn (fun x => (residual a b).eval x) (Set.Icc 0 b) by fun_prop)
    (show (0 : ℝ) ∈ Set.Ioo ((residual a b).eval b) ((residual a b).eval 0) from ⟨hb,h0⟩)
  exact ⟨μ,hμ.1,hμ.2,hzero⟩

/-- The full revised equality spectrum: b is a simple third quotient root,
with exactly one positive root below it and all three later roots above s.
There is no h(1)=0 premise. -/
theorem result (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∃ μ : ℝ, ∃ r : Multiset ℝ,
      (quotient a b (b*(b+2)-a)).charpoly.roots = {0}+{μ}+{b}+r ∧
      r.card = 3 ∧ 0 < μ ∧ μ < b ∧ b < a+b ∧ a+b < a+b+(b*(b+2)-a) ∧
      (∀ t ∈ r, a+b+(b*(b+2)-a) < t) := by
  classical
  let c := b*(b+2)-a
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hcb : b < c := by dsimp [c]; nlinarith [sq_pos_of_pos hb0]
  have hc0 : 0 < c := hb0.trans hcb
  have hg := SixSupportSpectralGap.result a b c ha hab hcb.le
  have hr := roots_relation a b
  change (quotient a b c).charpoly.roots = {0}+{b}+(residual a b).roots at hr
  obtain ⟨μ,hμ0,hμb,hμz⟩ := low_root a b ha hab
  have hμmem : μ ∈ (residual a b).roots :=
    (Polynomial.mem_roots (residual_nonzero a b)).mpr hμz
  have hμs : μ < a+b+c := by linarith
  have hFs : (residual a b).roots.countP (fun t => t < a+b+c) = 1 := by
    have htot := hg.2.2.2.1
    dsimp [below] at htot
    rw [hr] at htot
    simp [show 0 < a+b+c by positivity,show b < a+b+c by linarith] at htot
    omega
  have hs0 : SixSupportInertia.multiplicity a b c (a+b+c) = 0 := by
    rw [hg.2.2.2.2]
    exact if_neg (by rintro ⟨rfl,rfl,hc⟩; linarith)
  have hS := (quotient_geometry a b c ha0 hb0 hc0).2.1.1
  have hs := symmetric_charpoly a b c ha0 hab hcb.le
  have hq : (quotient a b c).charpoly = X*quintic a b c := by
    change (SixSupportLaplacianPolynomial.quotientOver a b c).charpoly = _
    rw [SixSupportLaplacianPolynomial.charpoly_zero_factor,quintic_eq_reduced]
  rw [← hq] at hs
  have hcard : (residual a b).roots.card = 4 := by
    have hn : (quotient a b c).charpoly.roots.card = 6 := by
      rw [← hs,hS.roots_charpoly_eq_eigenvalues]
      simp
    rw [hr] at hn
    simp only [Multiset.card_add,Multiset.card_singleton] at hn
    omega
  let r := (residual a b).roots.erase μ
  have herase : (residual a b).roots = {μ}+r := by
    simpa [r] using (Multiset.cons_erase hμmem).symm
  have hroot : (quotient a b c).charpoly.roots = {0}+{μ}+{b}+r := by
    rw [hr,herase]
    ac_rfl
  rw [herase] at hcard hFs
  simp only [Multiset.card_add,Multiset.card_singleton] at hcard
  simp [hμs] at hFs
  refine ⟨μ,r,hroot,by omega,hμ0,hμb,by linarith,by linarith,?_⟩
  intro t ht
  have hge : a+b+c ≤ t := le_of_not_gt (Multiset.countP_eq_zero.mp hFs t ht)
  have hne : t ≠ a+b+c := by
    intro heq
    subst t
    have hm : a+b+c ∈ (quotient a b c).charpoly.roots := by rw [hroot]; simp [ht]
    exact (Multiset.countP_eq_zero.mp hs0 (a+b+c) hm) rfl
  exact lt_of_le_of_ne hge hne.symm

/-- On endpoint one, the entire revised equality spectrum has smallest
positive root one and a monic residual cubic with every root strictly above s. -/
theorem endpoint_one (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (h1 : h a b (b*(b+2)-a) 1 = 0) :
    ∃ P : ℝ[X], P.Monic ∧ P.natDegree = 3 ∧
      SixSupportEndpointOneArithmetic.quartic a b (b*(b+2)-a) = (X-C b)*P ∧
      (∀ t ∈ P.roots, a+b+(b*(b+2)-a) < t) := by
  classical
  let c := b*(b+2)-a
  let F := SixSupportEndpointOneArithmetic.quartic a b c
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hcb : b < c := by dsimp [c]; nlinarith [sq_pos_of_pos hb0]
  obtain ⟨μ,r,hr,hcard,hμ0,hμb,hbs,has,hhigh⟩ := result a b ha hab
  change (quotient a b c).charpoly.roots = {0}+{μ}+{b}+r at hr
  have hr1 := SixSupportEndpointOneSpectrum.residual_roots a b c h1
  have hone : 1 ∈ (quotient a b c).charpoly.roots := by rw [hr1]; simp
  rw [hr] at hone
  simp only [Multiset.mem_add,Multiset.mem_singleton] at hone
  have hμ : μ = 1 := by
    rcases hone with ((hz | hm) | hb) | hm
    · norm_num at hz
    · exact hm.symm
    · linarith
    · have ht := hhigh 1 hm; linarith
  subst μ
  have hFroots : F.roots = {b}+r := by
    apply add_left_cancel (a := ({0}+{1} : Multiset ℝ))
    calc
      {0}+{1}+F.roots = (quotient a b c).charpoly.roots := hr1.symm
      _ = {0}+{1}+{b}+r := hr
      _ = ({0}+{1})+({b}+r) := by ac_rfl
  have hFcard := SixSupportEndpointOneSpectrum.residual_card a b c ha0 hab hcb.le h1
  have hFne : F ≠ 0 := by
    intro hz
    change F.roots.card = 4 at hFcard
    rw [hz,Polynomial.roots_zero,Multiset.card_zero] at hFcard
    omega
  have hbmem : b ∈ F.roots := by rw [hFroots]; simp
  have hbroot : F.eval b = 0 := (Polynomial.mem_roots hFne).mp hbmem
  let P := F /ₘ (X-C b)
  have hfP : F = (X-C b)*P :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hbroot).symm
  have hFm : F.Monic := by
    dsimp [F,SixSupportEndpointOneArithmetic.quartic]
    monicity!
  have hPm : P.Monic := by
    apply (Polynomial.monic_X_sub_C b).of_mul_monic_left
    rw [← hfP]
    exact hFm
  have hFdeg : F.natDegree = 4 := by
    dsimp [F,SixSupportEndpointOneArithmetic.quartic]
    compute_degree!
  have hPdeg : P.natDegree = 3 := by
    dsimp [P]
    rw [Polynomial.natDegree_divByMonic F (Polynomial.monic_X_sub_C b),
      Polynomial.natDegree_X_sub_C,hFdeg]
  have hPr : P.roots = r := by
    have hprod : (X-C b)*P ≠ 0 := by rw [← hfP]; exact hFne
    have hroots := congrArg Polynomial.roots hfP
    rw [Polynomial.roots_mul hprod,Polynomial.roots_X_sub_C,hFroots] at hroots
    exact (add_left_cancel hroots).symm
  refine ⟨P,hPm,hPdeg,hfP,?_⟩
  intro t ht
  rw [hPr] at ht
  exact hhigh t ht

#print axioms endpoint_one

#print axioms factorization
#print axioms derivative_negative
#print axioms result
end D5.S3.Combinatorics.SpectralGraph.SixSupportEqualitySpectrum
