/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubSource
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubSource
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub source identities. -/
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
namespace FiolDoubleHub

abbrev Edge (m : ℕ) := Bool × Option (Fin m)
abbrev Vertex (m : ℕ) := Option (Edge m)

-- Public mass assigns k to src and n-k to tgt. Thus the SOURCE arrow goes
-- from parent=tgt to child=src, matching the paper's convention exactly.
def src {m : ℕ} (e : Edge m) : Vertex m := some e
def tgt {m : ℕ} (e : Edge m) : Vertex m :=
  match e.2 with
  | none => none
  | some _ => some (e.1, none)

noncomputable def graph (m : ℕ) : SimpleGraph (Vertex m) :=
  D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.treeSupport src tgt Set.univ

noncomputable def automorphismOrder (m : ℕ) : ℕ := Nat.card ((graph m) ≃g graph m)

noncomputable def degree {m : ℕ} (v : Vertex m) : ℕ :=
  (Finset.univ.filter (fun e : Edge m => src e = v)).card +
    (Finset.univ.filter (fun e : Edge m => tgt e = v)).card

abbrev mass {m : ℕ} (n k : Edge m → ℕ) (v : Vertex m) : ℕ :=
  D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt n k v

noncomputable def J (k : ℕ) : ℝ :=
  (Nat.factorial (2*k) : ℝ) / ((Nat.factorial (k-1) : ℝ) * (Nat.factorial k : ℝ))

noncomputable def vertexWeight {m : ℕ} (n k : Edge m → ℕ) (v : Vertex m) : ℝ :=
  (Nat.factorial (mass n k v - 1) : ℝ) /
    (Nat.factorial (mass n k v - degree v + 2) : ℝ) *
  (∏ e ∈ Finset.univ.filter (fun e : Edge m => src e = v), J (k e)) *
  (∏ e ∈ Finset.univ.filter (fun e : Edge m => tgt e = v), J (n e-k e))

noncomputable def edgeBinom {m : ℕ} (n k : Edge m → ℕ) : ℝ :=
  ∏ e : Edge m, (Nat.choose (2*n e) (2*k e) : ℝ)

noncomputable def physicalWeight {m : ℕ} (n k : Edge m → ℕ) : ℝ :=
  edgeBinom n k * ∏ v : Vertex m, vertexWeight n k v

noncomputable def splitSource {m : ℕ} (n k : Edge m → ℕ) : Polynomial ℝ :=
  Polynomial.C (physicalWeight n k) *
  ∏ v : Vertex m, (1 + Polynomial.C ((-1 : ℝ) ^ degree v) * Polynomial.X ^ mass n k v)

-- All vertices, all allowed splits. This is the normalized all-vertex
-- construction labelled planarf2, not the editorially ambiguous rho product.
noncomputable def allVertexSource {m : ℕ} (n : Edge m → ℕ) : Polynomial ℝ :=
  ∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n, splitSource n k

-- An INDEPENDENT definition using the public native all-spin polynomial.
-- Equality with allVertexSource requires a real proof of the sign bridge.
noncomputable def allSpinSource {m : ℕ} (n : Edge m → ℕ) : Polynomial ℝ :=
  D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.treePoly src tgt n
    (physicalWeight n) (-1)

noncomputable def sourcePrefactor {m : ℕ} (n : Edge m → ℕ) : ℝ :=
  ((-2 : ℝ) ^ Fintype.card (Edge m)) * (-1 : ℝ) ^ (∑ e, n e) /
    ((∏ e : Edge m, (n e : ℝ)) * (automorphismOrder m : ℝ))

-- Independent formal generators indexed by r. A cutoff makes this a genuine
-- finite MvPolynomial. Coefficient stability for all cutoffs >=3 remains a
-- required proof; cutoff=3 is not assumed to encode the whole source series.
noncomputable def sourceTruncation (m cutoff : ℕ) :
    MvPolynomial ℕ (Polynomial ℝ) :=
  ∑ n ∈ Fintype.piFinset (fun _ : Edge m => Finset.Icc 2 cutoff),
    MvPolynomial.C (Polynomial.C (sourcePrefactor n) * allVertexSource n) *
      ∏ e : Edge m, MvPolynomial.X (2*n e-1)

noncomputable def targetMonomial (m : ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 5 2 + Finsupp.single 3 (2*m)

noncomputable def sourceCoefficient (m cutoff : ℕ) : Polynomial ℝ :=
  (sourceTruncation m cutoff).coeff (targetMonomial m)

-- Independent candidate closed form. No definition identifies it with sourceCoefficient.
noncomputable def H (r : ℕ) : Polynomial ℝ := 1 + Polynomial.X ^ r
noncomputable def S (r : ℕ) : Polynomial ℝ := ∑ j ∈ Finset.range r, Polynomial.X ^ j
noncomputable def U (d : ℕ) : Polynomial ℝ := if Odd d then S d else H d
noncomputable def V (d : ℕ) : Polynomial ℝ := if Odd d then S (d+1) else H (d+1)
noncomputable def W (d : ℕ) : Polynomial ℝ := if Odd d then S (d+2) else H (d+2)

def h (d : ℕ) : ℕ := if Odd d then 2*d else 2*d-2
def N (d : ℕ) : ℕ := if Odd d then d+1 else d+2

noncomputable def Q (d : ℕ) : Polynomial ℝ :=
  let x : ℝ := d
  H 2 * (Polynomial.C (2*x^4) * V d^2 +
    Polynomial.C ((3/2 : ℝ)*x^2*(x^2-1)) * U d * W d +
    Polynomial.C (4*x*(x-1)*(2*x-1)) * (1+Polynomial.X) * U d * V d +
    Polynomial.C (2*(x-1)*(2*x-3)) * (1+Polynomial.X)^2 * U d^2) +
  H 3 * (Polynomial.C (8*x*(2*x-1))*U d*V d +
    Polynomial.C (16*(x-1))*(1+Polynomial.X)*U d^2) +
  Polynomial.C 9 * H 4 * U d^2

noncomputable def R (m : ℕ) : Polynomial ℝ :=
  (1-Polynomial.X)^h (m+1) * Q (m+1)

noncomputable def homogeneousSplitSource {m : ℕ} (n k : Edge m → ℕ)
    (lambda1 lambda2 : ℂ) : ℂ :=
  (physicalWeight n k : ℂ) * ∏ v : Vertex m,
    (lambda1 ^ mass n k v + ((-1 : ℂ)^degree v)*lambda2 ^ mass n k v)

noncomputable def homogeneousTruncation (m cutoff : ℕ) (lambda1 lambda2 : ℂ) :
    MvPolynomial ℕ ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : Edge m => Finset.Icc 2 cutoff),
    MvPolynomial.C ((sourcePrefactor n : ℂ) *
      ∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n,
        homogeneousSplitSource n k lambda1 lambda2) *
      ∏ e : Edge m, MvPolynomial.X (2*n e-1)

noncomputable def homogeneousCoefficient (m cutoff : ℕ) (lambda1 lambda2 : ℂ) : ℂ :=
  (homogeneousTruncation m cutoff lambda1 lambda2).coeff (targetMonomial m)

noncomputable def expectedHomogeneousCoefficient (m : ℕ) (lambda1 lambda2 : ℂ) : ℂ :=
  (200*(12 : ℂ)^(2*m)) * ∑ j ∈ Finset.range (4*m+7),
    ((R m).coeff j : ℂ) * lambda1^(4*m+6-j) * lambda2^j

end FiolDoubleHub


private theorem exponent_iff {E : Type} [Fintype E] [DecidableEq E]
    (m : ℕ) (hE : Fintype.card E = 2*m+2) (n : E → ℕ) :
    (∑ e : E, Finsupp.single (2*n e-1) 1 : ℕ →₀ ℕ) =
      Finsupp.single 5 2 + Finsupp.single 3 (2*m) ↔
    (∀ e : E, n e = 2 ∨ n e = 3) ∧ (Finset.univ.filter (fun e : E => n e = 3)).card = 2 := by
  classical
  let ex : ℕ →₀ ℕ := ∑ e : E, Finsupp.single (2*n e-1) 1
  have heval (j : ℕ) : ex j = ∑ e : E, if 2*n e-1 = j then 1 else 0 := by
    simp [ex, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]
  have h5 : ex 5 = (Finset.univ.filter (fun e : E => n e = 3)).card := by
    rw [heval]
    have hi (e : E) : (2*n e-1 = 5) ↔ n e = 3 := by omega
    simp_rw [hi]
    simp
  have h3 : ex 3 = (Finset.univ.filter (fun e : E => n e = 2)).card := by
    rw [heval]
    have hi (e : E) : (2*n e-1 = 3) ↔ n e = 2 := by omega
    simp_rw [hi]
    simp
  constructor
  · intro h
    have hx : ex = Finsupp.single 5 2 + Finsupp.single 3 (2*m) := h
    constructor
    · intro e
      by_contra hn
      have hne3 : 2*n e-1 ≠ 3 := by omega
      have hne5 : 2*n e-1 ≠ 5 := by omega
      have hlocal : 1 ≤ ex (2*n e-1) := by
        rw [heval]
        have hb := Finset.single_le_sum (fun (i : E) (_ : i ∈ (Finset.univ : Finset E)) =>
          (Nat.zero_le (if 2*n i-1 = 2*n e-1 then 1 else 0))) (Finset.mem_univ e)
        simpa using hb
      rw [hx] at hlocal
      simpa [Finsupp.single_apply, hne3, hne5, Ne.symm hne3, Ne.symm hne5] using hlocal
    · have hv := congrArg (fun f : ℕ →₀ ℕ => f 5) hx
      simpa [h5] using hv
  · rintro ⟨hrange, hcount⟩
    have hsum : (Finset.univ.filter (fun e : E => n e = 2)).card +
        (Finset.univ.filter (fun e : E => n e = 3)).card = Fintype.card E := by
      calc
        _ = (∑ e : E, if n e = 2 then 1 else 0) +
              ∑ e : E, if n e = 3 then 1 else 0 := by simp
        _ = ∑ e : E, ((if n e = 2 then 1 else 0) + (if n e = 3 then 1 else 0)) := by
          rw [Finset.sum_add_distrib]
        _ = ∑ _ : E, 1 := by
          apply Finset.sum_congr rfl
          intro e he
          rcases hrange e with h | h <;> simp [h]
        _ = _ := by simp
    have hcount2 : (Finset.univ.filter (fun e : E => n e = 2)).card = 2*m := by omega
    change ex = _
    ext j
    by_cases hj5 : j = 5
    · subst j; simpa [h5] using hcount
    by_cases hj3 : j = 3
    · subst j; simpa [h3] using hcount2
    have hz : ex j = 0 := by
      rw [heval]
      apply Finset.sum_eq_zero
      intro e he
      rcases hrange e with hn | hn <;> simp [hn, Ne.symm hj3, Ne.symm hj5]
    simp [hz, Finsupp.single_apply, hj5, hj3, Ne.symm hj5, Ne.symm hj3]

private theorem generator_coefficient {E : Type} [Fintype E] [DecidableEq E]
    {R : Type} [CommSemiring R] (m : ℕ) (hE : Fintype.card E = 2*m+2) (n : E → ℕ) :
    ((∏ e : E, MvPolynomial.X (2*n e-1) : MvPolynomial ℕ R).coeff
      (Finsupp.single 5 2 + Finsupp.single 3 (2*m))) =
    if (∀ e : E, n e = 2 ∨ n e = 3) ∧
      (Finset.univ.filter (fun e : E => n e = 3)).card = 2 then 1 else 0 := by
  classical
  have hp : (∏ e : E, MvPolynomial.X (2*n e-1) : MvPolynomial ℕ R) =
      MvPolynomial.monomial (∑ e : E, Finsupp.single (2*n e-1) 1) 1 := by
    simpa [MvPolynomial.X] using
      (MvPolynomial.monomial_sum_prod (Finset.univ : Finset E)
        (fun e => Finsupp.single (2*n e-1) 1) (fun _ : E => (1 : R))).symm
  rw [hp, MvPolynomial.coeff_monomial]
  simp only [exponent_iff m hE n]

-- No multiplicity factorial appears: the formal generator coefficient is 1
-- for each exactly-two-edge assignment and 0 for all other total tuples.
theorem coefficient_extract {E : Type} [Fintype E] [DecidableEq E]
    {R : Type} [CommSemiring R] (m cutoff : ℕ)
    (hE : Fintype.card E = 2*m+2) (a : (E → ℕ) → R) :
    ((∑ n ∈ Fintype.piFinset (fun _ : E => Finset.Icc 2 cutoff),
      MvPolynomial.C (a n) * ∏ e : E, MvPolynomial.X (2*n e-1) :
      MvPolynomial ℕ R).coeff
        (Finsupp.single 5 2 + Finsupp.single 3 (2*m))) =
    ∑ n ∈ (Fintype.piFinset (fun _ : E => Finset.Icc 2 cutoff)).filter
      (fun n => (∀ e : E, n e = 2 ∨ n e = 3) ∧
        (Finset.univ.filter (fun e : E => n e = 3)).card = 2), a n := by
  classical
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, generator_coefficient m hE]
  simp [Finset.sum_filter, mul_ite]


theorem pair_sum {E : Type} [Fintype E] [DecidableEq E]
    {R : Type} [AddCommMonoid R] (cutoff : ℕ) (hc : 3 ≤ cutoff)
    (a : (E → ℕ) → R) :
    (∑ n ∈ (Fintype.piFinset (fun _ : E => Finset.Icc 2 cutoff)).filter
      (fun n => (∀ e : E, n e = 2 ∨ n e = 3) ∧
        (Finset.univ.filter (fun e : E => n e = 3)).card = 2), a n) =
    ∑ A ∈ (Finset.univ : Finset E).powersetCard 2,
      a (fun e => if e ∈ A then 3 else 2) := by
  classical
  let pick (n : E → ℕ) := Finset.univ.filter (fun e : E => n e = 3)
  let assign (A : Finset E) (e : E) := if e ∈ A then 3 else 2
  have hassign (n : E → ℕ) (hr : ∀ e, n e = 2 ∨ n e = 3) :
      assign (pick n) = n := by
    funext e
    rcases hr e with h | h <;> simp [assign, pick, h]
  have hpick (A : Finset E) : pick (assign A) = A := by
    ext e
    simp [pick, assign]
  refine Finset.sum_bij (fun n _ => pick n) ?_ ?_ ?_ ?_
  · intro n hn
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hn).2.2⟩
  · intro n hn n' hn' heq
    have h := hassign n (Finset.mem_filter.mp hn).2.1
    have h' := hassign n' (Finset.mem_filter.mp hn').2.1
    rw [← h, ← h', heq]
  · intro A hA
    refine ⟨assign A, Finset.mem_filter.mpr ⟨?_, ?_⟩, hpick A⟩
    · apply Fintype.mem_piFinset.mpr
      intro e
      dsimp [assign]
      split_ifs <;> exact Finset.mem_Icc.mpr (by omega)
    · constructor
      · intro e
        dsimp [assign]
        split_ifs <;> omega
      · change (pick (assign A)).card = 2
        rw [hpick]
        exact (Finset.mem_powersetCard.mp hA).2
  · intro n hn
    change a n = a (assign (pick n))
    rw [hassign n (Finset.mem_filter.mp hn).2.1]


namespace FiolDoubleHub

-- The actual independent formal source selects every two-edge subset once.
theorem source_pair_formula (m cutoff : ℕ) (hc : 3 ≤ cutoff) :
    sourceCoefficient m cutoff =
      ∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,
        Polynomial.C (sourcePrefactor (fun e => if e ∈ A then 3 else 2)) *
          allVertexSource (fun e => if e ∈ A then 3 else 2) := by
  have hE : Fintype.card (Edge m) = 2*m+2 := by simp [Edge]; omega
  change ((∑ n ∈ Fintype.piFinset (fun _ : Edge m => Finset.Icc 2 cutoff),
    MvPolynomial.C (Polynomial.C (sourcePrefactor n) * allVertexSource n) *
      ∏ e : Edge m, MvPolynomial.X (2*n e-1)).coeff
      (Finsupp.single 5 2 + Finsupp.single 3 (2*m))) = _
  rw [coefficient_extract m cutoff hE, pair_sum cutoff hc]

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
