import GRH.Lib.General.Algebra.JetChainRule
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

A step of the proof of: Sharpness of Katz's divisibility for invariant derivatives on a CM formal
group.

This file: Coefficients of substituted p-adic series; bounds by products over columns; lowest
terms. -/

open Finset _root_.Nat Fin Finsupp IsUltrametricDist MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {I X R : Type} [CommRing R] {H H' : MvPowerSeries X
  ℂ_[p]} {D D' : X →₀ ℕ} {N k k' r r'} {a : ℂ_[p]} (c : X → _) (g : PowerSeries ℂ_[p]) (w : X → ℕ)

lemma HasLargeSplit.mono : HasLargeSplit N k D r → r' ≤ r →
  HasLargeSplit N k D r' := by grind [HasLargeSplit]

lemma HasLargeSplit.mul : HasLargeSplit N k D r → HasLargeSplit N k' D' r' →
  (_ : 0 ≤ r' := by bound) → HasLargeSplit N (k + k') (D + D') (r
  * r') := fun ⟨α, _⟩ ⟨β, _⟩ _ ↦ ⟨append α β, by
  rw [sum_univ_add, prod_univ_add]; simp_all; gcongr <;> simp_all⟩

/-- k copies carry H: every exponent α is a sum of k exponents on which the product of N is at
least |coeff_α H|. -/
def IsCarriedBy N k H := ∀ α, HasLargeSplit N k α ‖@coeff X ℂ_[p] _ α H‖

lemma IsCarriedBy.mul (h : IsCarriedBy N k H) (h' : IsCarriedBy N k' H') :
  IsCarriedBy N (k + k') (H * H') := fun α ↦ by
  have ⟨(a, b), _⟩ := H.coeff_mul α H' ▸ exists_norm_finsetSum_le_of_nonempty ⟨(0, α), by simp⟩ _
  convert ((h a).mul (h' b)).mono <;> aesop

/-- Let f_i be finitely many series over ℂ_p in finitely many variables, without
constant term, s a series, α an exponent.
Some exponent e with |e| ≤ |α| satisfies |coeff_α(g(f)·s)| ≤ |coeff_α(∏f_i^{e_i}·s)| for
every series g with integral coefficients. -/
lemma exists_monomial_max_norm_coeff [Fintype X] [Fintype I] {f} {h : @HasSubst I X ℂ_[p] _ f} S
    (e : S = ((substAlgHom h).1.comp (@seriesToCp p ..)).range) s α : ∃ e :
    _ →₀ _, e.degree ≤ α.degree ∧ ∀ g ∈ S, ‖coeff α (g * s)‖ ≤ ‖coeff α (e.prod (f · ^ ·) * s)‖ :=
    (Set.exists_max_image _ _ (finite_of_degree_le _) ⟨0, by simp⟩).imp fun _ ↦ .imp_right (by
  have k := (coeff_truncTotal_mul_truncTotal_eq_coeff_mul · s α.degree.lt_add_one)
  simp [e]; intro H g
  rw [← k, truncTotal_subst_eq_truncTotal_truncTotal_subst (h.1 · |>.eq_zero), k]
  simpa [subst_coe, truncTotal, truncFinset, Finset.sum_mul, MvPolynomial.aeval_monomial,
    ← Algebra.smul_def] using! norm_sum_le_of_forall_le_of_nonneg (by simp) fun d _ ↦
    norm_mul_le_of_le (g d).2 (H d (by aesop)))

/-- The series f agrees with the monomial c·z^m at all exponents whose w-weight is at most that
of m. -/
def IsLowestTerm f m (c : R) := ∀ d, d.weight w ≤ m.weight w → coeff d f = (monomial m c).coeff d

lemma IsLowestTerm.mul {w f g c d} : @IsLowestTerm X R _ w f D c → IsLowestTerm w g D' d →
  IsLowestTerm w (f * g) (D + D') (c * d) := by
  simp [IsLowestTerm, ← monomial_mul_monomial, coeff_mul]; congr! 1
  simp_all; grind [coeff_monomial]

variable [Fintype X]

open MvPolynomial

/-- For g ∈ ℂ_p[[t]] and a linear form ∑ c_x z_x in finitely many variables, the coefficient of
z^D in g(∑ c_x z_x) is (∏ c_x^{D_x}) · |D|! · g_{|D|} / ∏ D_x!, with |D| the total degree
and g_n the n-th coefficient of g. -/
@[simp] lemma coeff_subst_linearSeries : (g.subst (linearSeries c)).coeff D = (∏ x, c x ^ D x) *
    (D.degree ! * g.coeff D.degree) / ∏ x, ↑(D x)! := by
  simpa [aeval_monomial, prod_fintype, smul_pow, prod_smul, -aeval_eq_bind₁, X_pow_eq_monomial,
    linSubst, ← monomial_sum_one, ← single_finsetSum, field, Finset.prod_eq_zero_iff,
    degree_eq_sum, mul_comm] using! jet_subst_linearSeries _ (monomial D 1) g

@[simp] lemma rescale_subst_linearSeries : rescale (fun _ ↦ a) (g.subst (linearSeries c)) =
  (g.rescale a).subst (linearSeries c) := ext (by simp [prod_pow_eq_pow_sum, degree_eq_sum, field])
