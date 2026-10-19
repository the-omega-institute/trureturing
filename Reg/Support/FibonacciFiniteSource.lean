import Reg.Support.FibonacciConsensus

namespace Reg.Support.FibonacciFiniteSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open Filter Topology
noncomputable section

/-- A supported original Omega that is L0 after M has the zero scalar tail after M. -/
theorem omega_tail_zero (alpha : ℕ → Label) (x : ℕ → ℝ)
    (omega : OperationOmega alpha x) (M : ℕ)
    (tail : ∀ p, M ≤ p → alpha p = .L0) : ∀ p, M ≤ p → x p = 0 := by
  obtain ⟨path,h0,edges,support,recurrence⟩ := omega
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  intro p hp
  have iteration (n : ℕ) : x p = (-g)^n * x (p+n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih,recurrence (p+n),tail (p+n) (by omega)]
      simp only [branch,shift]
      rw [pow_succ]
      ring_nf
  have bound (n : ℕ) : |x p| ≤ phi * g^n := by
    have upper : supportUpper (path (p+n)) ≤ phi := by
      cases path (p+n) <;> simp [supportUpper,phi]
    have scalar : |x (p+n)| ≤ phi := abs_le.mpr
      ⟨by linarith [(support (p+n)).1],(support (p+n)).2.trans upper⟩
    rw [iteration n,abs_mul,abs_pow,abs_neg,abs_of_pos hgpositive]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left scalar (pow_nonneg hgpositive.le n)
  have converges : Tendsto (fun n : ℕ => phi*g^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hgpositive.le hgone).const_mul phi
  have zero : |x p| ≤ 0 := ge_of_tendsto converges (Eventually.of_forall bound)
  exact abs_eq_zero.mp (le_antisymm zero (abs_nonneg _))

/-- The original clipped, owned observation of a zero coordinate is color 1
throughout the entire closed radius range, including theta = lam. -/
theorem zero_observation (o : Ownership) (theta error : ℝ)
    (htheta : theta ≤ lam) (herror : |error| ≤ theta) : observe o 0 error = 1 := by
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  have he := abs_le.mp (herror.trans htheta)
  have hl : -1 ≤ error := by dsimp [lam,T2] at he; linarith
  have hu : error ≤ phi := by dsimp [lam,T2,phi] at he ⊢; linarith
  have c1 : cut 1 < error := by norm_num [cut,lam,T2] at he ⊢; linarith
  have c2 : error < cut 2 := by norm_num [cut,lam,T2,g] at he ⊢; nlinarith
  simp only [observe,zero_add,clip,min_eq_right hu,max_eq_right hl,readout,
    not_lt.mpr c1.le,ne_of_gt c1,if_false,c2,if_true]

/-- Every actual finite-source record has an eventual constant Color-1 input,
without an eventual zero-error assumption. -/
theorem record_tail_one (o : Ownership) (theta : ℝ) (htheta : theta ≤ lam)
    (alpha : ℕ → Label) (r : ℕ → Color)
    (record : OperationRecord o theta .closed alpha r) (finite : OperationFiniteSource alpha) :
    ∃ M, ∀ p, M ≤ p → r p = 1 := by
  obtain ⟨x,omega,err,bound,observed⟩ := record
  obtain ⟨M,tail⟩ := finite
  have zero := omega_tail_zero alpha x omega M tail
  refine ⟨M,?_⟩
  intro p hp
  rw [← observed p,zero p hp]
  exact zero_observation o theta (err p) htheta (bound p)

/-- Any full closed candidate for an eventual Color-1 record is itself a finite source. -/
theorem compatible_tail_finite (theta : ℝ) (htheta : theta ≤ lam)
    (beta : ℕ → Label) (y : ℕ → ℝ) (omega : OperationOmega beta y)
    (r : ℕ → Color) (compatible : ∀ p, ClosedExpanded theta (r p) (y p))
    (M : ℕ) (tail : ∀ p, M ≤ p → r p = 1) :
    ∀ p, M ≤ p → beta p = .L0 := by
  obtain ⟨path,h0,edges,support,recurrence⟩ := omega
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  have lower (p : ℕ) (hp : M ≤ p) : cut 1-lam ≤ y p := by
    have h := compatible p
    rw [tail p hp] at h
    exact (sub_le_sub_left htheta _).trans h.2.1
  have upper (p : ℕ) (hp : M ≤ p) : y p ≤ cut 2+lam := by
    have h := compatible p
    rw [tail p hp] at h
    have hy : y p ≤ cut 2 + theta := by simpa using h.2.2
    exact hy.trans (by linarith)
  intro p hp
  have currLo := lower p hp
  have currHi := upper p hp
  have nextLo := lower (p+1) (by omega)
  have nextHi := upper (p+1) (by omega)
  have productLo := mul_le_mul_of_nonneg_left nextLo hgpositive.le
  have productHi := mul_le_mul_of_nonneg_left nextHi hgpositive.le
  have recurrenceValue := recurrence p
  cases hb : beta p <;> rw [hb] at recurrenceValue <;>
    simp only [branch,shift] at recurrenceValue
  · norm_num [cut,lam,T2,g] at currLo productLo recurrenceValue
    nlinarith [ht]
  · norm_num [cut,lam,T2,g] at currHi productHi recurrenceValue
    nlinarith [ht]
  · norm_num [cut,lam,T2,g] at currHi productHi recurrenceValue
    nlinarith [ht]
  · norm_num [cut,lam,T2,g] at currHi productHi recurrenceValue
    nlinarith [ht]

/-- Full compatible candidates for actual finite records become finite, even at lam. -/
theorem compatible_finite (o : Ownership) (theta : ℝ) (htheta : theta ≤ lam)
    (alpha : ℕ → Label) (r : ℕ → Color)
    (record : OperationRecord o theta .closed alpha r) (finite : OperationFiniteSource alpha)
    (beta : ℕ → Label) (y : ℕ → ℝ) (omega : OperationOmega beta y)
    (compatible : ∀ p, ClosedExpanded theta (r p) (y p)) : OperationFiniteSource beta := by
  obtain ⟨M,tail⟩ := record_tail_one o theta htheta alpha r record finite
  exact ⟨M,compatible_tail_finite theta htheta beta y omega r compatible M tail⟩

#print axioms omega_tail_zero
#print axioms zero_observation
#print axioms record_tail_one
#print axioms compatible_finite
end
end Reg.Support.FibonacciFiniteSource
