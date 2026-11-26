import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.Base
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Absolutely integrally closed rings: definition and permanence; Frobenius ring map. Normed
fields over Q_p; elementary lemmas on adic separation and completeness. Ring maps to p-adically
separated rings agree if they agree on dense elements. -/

open IsLocalization Polynomial Ideal Padic

/-- The ring endomorphism x ↦ x^(p^f) of a commutative ring B in which the prime p is zero. -/
@[simps! -fullyApplied] def frobPow {p B} [Fact (Nat.Prime p)] [CommRing B] (h : (p : B) = 0)
    (f : ℕ) : B →+* B := .mk' (powMonoidHom (p ^ f)) (by simp [add_pow_prime_pow_eq Fact.out, *])

/-- A is absolutely integrally closed: every monic polynomial over A of positive degree has a
root in A. -/
class IsAIC A [CommRing A] where exists_root P : Monic P → 0 < P.natDegree → ∃ x : A, P.IsRoot x

variable {A B K} [CommRing A] [CommRing B] [Field K] [h : IsAIC A] {f : A →+* B} {P : B[X]}

instance [IsAlgClosed K] : IsAIC K := ⟨fun _ _ ↦ (IsAlgClosed.eval_surjective ·.ne' 0)⟩

namespace IsAIC

lemma isAlgClosed (h : IsAIC K) : IsAlgClosed K := .of_exists_root _ (h.1 · · ·.natDegree_pos)

lemma exists_eval₂_eq_zero (f : B →+* A) (hP : Monic P) : 0 < P.natDegree → ∃ x,
  P.eval₂ f x = 0 := by nontriviality A; simpa [*, eval_map] using h.1 _ (hP.map f)

lemma of_isIntegrallyClosedIn A [CommRing A] [h : IsAIC A] [Algebra B A] [i :
  IsIntegrallyClosedIn B A] : IsAIC B := ⟨fun _ ↦
  (h.exists_eval₂_eq_zero _ · · |>.elim fun _ _ ↦ (i.2.1 (by tauto)).imp (i.rec (by aesop)))⟩

lemma exists_root_of_coeffs_subset_range : ↑P.coeffs ⊆ Set.range f → P.Monic → 0 < P.natDegree →
  ∃ x, P.IsRoot x := by grind [=_ lifts_iff_coeffs_subset_range, →
  lifts_and_natDegree_eq_and_monic, → exists_root, → IsRoot.map (f := f)]

lemma exists_pow_eq n [q : NeZero n] a : ∃ x : A, x ^ n = a := by
  nontriviality A; simpa [q.pos] using h.1 _ (monic_X_pow_sub_C a q.1)

/-- In a nonzero absolutely integrally closed ring A, for n > 1 and any c, b in A, the equation
x^n − cx = b has a solution x in A. -/
lemma exists_pow_sub_mul_eq [Nontrivial A] n [q : Fact (1 < n)] c b : ∃ x : A, x ^ n - c * x = b :=
  have H := (isMonicOfDegree_X_pow ..).sub (natDegree_linear_le.trans_lt q.1)
  by simpa [← sub_sub] using h.1 _ H.2 (H.1 ▸ q.1.le :)

lemma of_surjective (s : (⇑f).Surjective) : IsAIC B :=
  ⟨fun _ ↦ h.exists_root_of_coeffs_subset_range fun x _ ↦ s x⟩

/-- If every monic polynomial of positive degree over A has a root in A, the same holds for the
localisation B of A at any submonoid S. -/
lemma of_isLocalization (S : Submonoid A) [Algebra A B] [IsLocalization S B] : IsAIC B :=
    ⟨fun P _ _ ↦ (h.exists_root_of_coeffs_subset_range
  ((lifts_iff_coeffs_subset_range _).1 (scaleRoots_commonDenom_mem_lifts S P
  (by aesop))) (by simpa [Monic]) (by simpa)).elim fun x _ ↦ (map_units ..).dvd.imp fun y e ↦
  ((map_units ..).pow _).mul_right_eq_zero.1 (by rwa [← scaleRoots_eval_mul, ← e])⟩

variable [IsDomain B]

/-- Let A be absolutely integrally closed, f: A → B a ring map to a domain, and P a monic
polynomial over A. Every root x in B of the image of P is f(a) for some root a of P in A. -/
lemma exists_root_map_eq {x P} (hP : Monic P) : P.eval₂ f x = 0 → ∃ a, P.IsRoot a ∧ f a = x := by
  induction' _ : P.natDegree generalizing P; aesop
  obtain ⟨_, _, _, ⟨⟩⟩ := f.domain_nontrivial, (h.1 P hP (by lia)).imp fun _ ↦ dvd_iff_isRoot.2
  simp_all [natDegree_mul', Monic.def, leadingCoeff_monic_mul]; grind

/-- If A is absolutely integrally closed and f: A → B is a ring map to a domain, every element
of B integral over A lies in f(A). -/
lemma mem_range_of_isIntegralElem {x} : f.IsIntegralElem x → x ∈ f.range :=
  .rec (by grind [exists_root_map_eq, f.mem_range])

end IsAIC

/-- The statement that p is prime, as a class that fixes the prime p in scope. -/
class ThePrime (p : outParam ℕ) extends Fact p.Prime

/-- A normed field F that is a normed algebra over Q_p, not necessarily complete; the prime p is
read off from F. -/
class PadicField F (p : outParam ℕ) [Fact p.Prime] [NormedField F] extends NormedAlgebra ℚ_[p] F

/-- For a prime ℓ, a choice of ring isomorphism ιℓ from ℂ to the algebraic closure of Q_ℓ. -/
class PadicIso (ℓ : outParam ℕ) [Fact ℓ.Prime] where ιℓ : ℂ ≃+* PadicAlgCl ℓ

export PadicIso (ιℓ)

/-- A p-adic place of ℂ: a choice of ring homomorphism ιₚ from ℂ to C_p. -/
class PadicPlace (p : outParam ℕ) [Fact p.Prime] where ιₚ : ℂ →+* ℂ_[p]

export PadicPlace (ιₚ)

variable {R} (N) [CommRing R] [AddCommGroup N] [Module R N] {π x y : R} {p n : ℕ} [Fact p.Prime] {F}
  [NormedField F] [PadicField F p] {S} [CommRing S]

noncomputable instance : PadicField ℂ_[p] p where

noncomputable instance : PadicField (PadicAlgCl p) p where

lemma norm_p_eq_inv : ‖(p : F)‖ = (↑p)⁻¹ := mod_cast (norm_algebraMap' ..).trans norm_p

lemma norm_p_lt_one : ‖(p : F)‖ < 1 := by simp [norm_p_eq_inv, ← norm_p]

lemma Nat.Coprime.norm_natCast_eq_one (h : p.Coprime n) F [NormedField F] [PadicField F p] :
    ‖(n : F)‖ = 1 := mod_cast (norm_algebraMap' ..).trans (norm_natCast_eq_one_iff.2 h)

/-- Let T be a map between commutative rings R and S with T(πa) = ϖT(a) for all a, ϖ a
non-zero-divisor, and ϖ ∣ T(a) implying π ∣ a. Then ϖ^n ∣ T(x) implies π^n ∣ x. -/
lemma pow_dvd_of_map {ϖ} {T : R → S} (hT : ∀ a, T (π * a) = ϖ * T a) (h₀ : ϖ ∈ nonZeroDivisors S)
    (h : ∀ a, ϖ ∣ T a → π ∣ a) (H : ϖ ^ n ∣ T x) : π ^ n ∣ x := by
  induction n generalizing x <;> simp_all [pow_succ', dvd_def, mul_assoc]
  grind [mul_cancel_left_mem_nonZeroDivisors]

lemma smodEq_span_pow_iff_dvd : x ≡ y [SMOD (span {π} ^ n • ⊤ : Ideal R)] ↔ π ^ n ∣ x - y := by
  simp [SModEq.sub_mem, span_singleton_pow, mem_span_singleton]

lemma eq_of_forall_pow_dvd_sub π [IsHausdorff (span {π}) R] (h : ∀ n, π ^ n ∣ x - y) : x = y :=
  IsHausdorff.eq_iff_smodEq.2 (smodEq_span_pow_iff_dvd.2 <| h ·)

lemma isUnit_of_dvd_sub [IsAdicComplete (span {π}) R] (u : IsUnit y) (h : π ∣ x - y) : IsUnit x :=
  by simpa [sub_mul] using mem_jacobson_bot.1 (HenselianRing.jac (mem_span_singleton.2 h)) ↑u.unit⁻¹

omit [Fact p.Prime] in
lemma isAdicComplete_over_base [Algebra S R] (h : IsAdicComplete (span {(p : R)}) R) :
  IsAdicComplete (span {(p : S)}) R := (IsAdicComplete.map_algebraMap_iff ..).1 (by simpa)

/-- For π in R and an R-module N, the map on sequences in N sending (x_j) to (x_j − π x_{j+1}). -/
def shiftDiff (π : R) (x : ℕ → N) j := x j - π • x (j + 1)

/-- If the maps `shiftDiff` attached to x and to y, for the commutative ring R as a module over
itself, are both surjective, then R is precomplete for the ideal (x,y): every (x,y)-adic
Cauchy sequence has a limit. -/
lemma isPrecomplete_of_shiftDiff_surjective (ha : (shiftDiff R x).Surjective) (hb :
  (shiftDiff R y).Surjective) : IsPrecomplete (span {x, y}) R := ⟨by
  simp_intro f hf [SModEq.sub_mem]
  choose u v e using by simpa [span_singleton_pow, ← span_insert, mem_span_pair] using fun n ↦
    sup_pow_add_le_pow_sup_pow (span_insert x _ ▸ hf (Nat.le_add_right (n + n) 2) :)
  obtain ⟨⟨U, rfl⟩, V, rfl⟩ := ha u, hb v
  peel (⟨_, Nat.rec rfl (by grind [shiftDiff, smul_eq_mul, e ·])⟩ :
    ∃ L, ∀ n, L = f (n + n) + -U n * x ^ n + -V n * y ^ n)
  aesop (add simp sub_add_eq_sub_sub, 1% [mul_mem_left, pow_mem_pow])⟩

lemma ringHom_ext_of_approx {p : ℕ} {A R} [CommRing A] [CommRing R] [IsHausdorff (.span
    {(p : R)}) R] {F G : A →+* R} (h : ∀ a n, ∃ b, F b = G b ∧ p.cast ^ n ∣ a - b) : F = G := F.ext
  fun a ↦ eq_of_forall_pow_dvd_sub p (h a · |>.rec fun b ⟨_, c, _⟩ ↦ by simp_all [sub_eq_iff_eq_add,
  dvd_sub])
