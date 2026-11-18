/- GID: D5/S3/Quantum/Fermionic/SlaterCutPhase
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/SlaterCutPhase
   mirror-E: none(waiver:uniform-occupation-phase)
   anchors: []
   utility: none
   digest: A cut without four alternating sites preserves the fixed-occupation marginal spectrum under the row-shuffle sign. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Tactic.Ring

/-! # Occupied-site shuffle phases at a spatial cut -/

@[expose] public section

namespace D5.S3.Quantum.Fermionic.SlaterCutPhase

open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

/-- Four increasingly ordered sites alternate between the sides of a cut. -/
def Alternates (I : Set ι) : Prop :=
  ∃ x y z w : ι, x < y ∧ y < z ∧ z < w ∧
    ((x ∈ I ∧ y ∉ I ∧ z ∈ I ∧ w ∉ I) ∨
     (x ∉ I ∧ y ∈ I ∧ z ∉ I ∧ w ∈ I))

private theorem exists_hole (S : Set ι) (h : ¬ S.OrdConnected) :
    ∃ x y z : ι, x < y ∧ y < z ∧ x ∈ S ∧ y ∉ S ∧ z ∈ S := by
  classical
  by_contra hn
  apply h
  constructor
  intro x hx z hz y hy
  by_contra hny
  have hxy : x ≠ y := fun e => hny (e ▸ hx)
  have hyz : y ≠ z := fun e => hny (e.symm ▸ hz)
  exact hn ⟨x, y, z, lt_of_le_of_ne hy.1 hxy, lt_of_le_of_ne hy.2 hyz, hx, hny, hz⟩

/-- A cut has no four-site alternation exactly when one side is order connected. -/
theorem not_alternates_iff (I : Set ι) :
    ¬ Alternates I ↔ I.OrdConnected ∨ (Iᶜ).OrdConnected := by
  classical
  constructor
  · intro halt
    by_cases hI : I.OrdConnected
    · exact Or.inl hI
    right
    obtain ⟨x, y, z, hxy, hyz, hx, hy, hz⟩ := exists_hole I hI
    have hbound (u : ι) (hu : u ∉ I) : x < u ∧ u < z := by
      constructor
      · by_contra! hux
        have hne : u ≠ x := fun e => hu (e.symm ▸ hx)
        exact halt ⟨u, x, y, z, lt_of_le_of_ne hux hne, hxy, hyz, Or.inr ⟨hu, hx, hy, hz⟩⟩
      · by_contra! hzu
        have hne : z ≠ u := fun e => hu (e ▸ hz)
        exact halt ⟨x, y, z, u, hxy, hyz, lt_of_le_of_ne hzu hne, Or.inl ⟨hx, hy, hz, hu⟩⟩
    constructor
    intro u hu v hv t ht
    change t ∉ I
    intro hti
    have hut : u ≠ t := fun e => hu (e.symm ▸ hti)
    have htv : t ≠ v := fun e => hv (e ▸ hti)
    exact halt ⟨x, u, t, v, (hbound u hu).1, lt_of_le_of_ne ht.1 hut,
      lt_of_le_of_ne ht.2 htv, Or.inl ⟨hx, hu, hti, hv⟩⟩
  · rintro (hI | hJ) ⟨x, y, z, w, hxy, hyz, hzw, hleft | hright⟩
    · exact hleft.2.1 (hI.out' hleft.1 hleft.2.2.1 ⟨hxy.le, hyz.le⟩)
    · exact hright.2.2.1 (hI.out' hright.2.1 hright.2.2.2 ⟨hyz.le, hzw.le⟩)
    · exact (show z ∉ I from hJ.out' hleft.2.1 hleft.2.2.2 ⟨hyz.le, hzw.le⟩) hleft.2.2.1
    · exact (show y ∉ I from hJ.out' hright.1 hright.2.2.1 ⟨hxy.le, hyz.le⟩) hright.2.1

/-- The number of occupied dropped sites that pass occupied retained sites. -/
def crossCount (a b : Finset ι) : ℕ :=
  ∑ i ∈ a, ∑ j ∈ b, if j < i then 1 else 0

private theorem lt_iff_of_inside
    {S : Set ι} (hS : S.OrdConnected) {i p j : ι}
    (hi : i ∈ S) (hp : p ∈ S) (hj : j ∉ S) : j < i ↔ j < p := by
  constructor
  · intro hji
    by_contra! hpj
    exact hj (hS.out' hp hi ⟨hpj, hji.le⟩)
  · intro hjp
    by_contra! hij
    exact hj (hS.out' hi hp ⟨hij, hjp.le⟩)

private theorem gt_iff_of_inside
    {S : Set ι} (hS : S.OrdConnected) {j p i : ι}
    (hj : j ∈ S) (hp : p ∈ S) (hi : i ∉ S) : j < i ↔ p < i := by
  constructor
  · intro hji
    by_contra! hip
    exact hi (hS.out' hj hp ⟨hji.le, hip⟩)
  · intro hpi
    by_contra! hij
    exact hi (hS.out' hp hj ⟨hpi.le, hij⟩)

/-- When the retained side is connected, each dropped particle crosses all or none
of the retained particles. -/
private theorem crossCount_retained_connected
    {I : Set ι} (hI : I.OrdConnected) {p : ι} (hp : p ∈ I)
    (a b : Finset ι) (ha : (↑a : Set ι) ⊆ I) (hb : (↑b : Set ι) ⊆ Iᶜ) :
    crossCount a b = a.card * (b.filter (· < p)).card := by
  unfold crossCount
  apply Finset.sum_const_nat
  intro i hi
  calc
    (∑ j ∈ b, if j < i then 1 else 0) = ∑ j ∈ b, if j < p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [lt_iff_of_inside hI (ha hi) hp (hb hj)]
    _ = (b.filter (· < p)).card := by simp

/-- When the dropped side is connected, each retained particle crosses all or none
of the dropped particles. -/
private theorem crossCount_dropped_connected
    {I : Set ι} (hJ : (Iᶜ).OrdConnected) {p : ι} (hp : p ∉ I)
    (a b : Finset ι) (ha : (↑a : Set ι) ⊆ I) (hb : (↑b : Set ι) ⊆ Iᶜ) :
    crossCount a b = b.card * (a.filter (p < ·)).card := by
  unfold crossCount
  rw [Finset.sum_comm]
  apply Finset.sum_const_nat
  intro j hj
  calc
    (∑ i ∈ a, if j < i then 1 else 0) = ∑ i ∈ a, if p < i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [gt_iff_of_inside hJ (hb hj) hp (fun hni => hni (ha hi))]
    _ = (a.filter (p < ·)).card := by simp

/-- On a fixed occupation sector the shuffle phase factors into a phase
on each side of a cut without alternation. -/
private theorem phase_factors {I : Set ι} (h : ¬ Alternates I) (k : ℕ) :
    ∃ l r : Finset ι → ℕ,
      ∀ a b : Finset ι, (↑a : Set ι) ⊆ I → (↑b : Set ι) ⊆ Iᶜ →
        a.card + b.card = k → crossCount a b = l a + r b := by
  classical
  rcases (not_alternates_iff I).1 h with hI | hJ
  · by_cases hne : I.Nonempty
    · obtain ⟨p, hp⟩ := hne
      refine ⟨fun _ => 0, fun b => (k - b.card) * (b.filter (· < p)).card, ?_⟩
      intro a b ha hb hk
      rw [crossCount_retained_connected hI hp a b ha hb]
      simp [← hk]
    · refine ⟨fun _ => 0, fun _ => 0, ?_⟩
      intro a b ha _ _
      have he : a = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i hi => hne ⟨i, ha hi⟩
      simp [he, crossCount]
  · by_cases hne : (Iᶜ).Nonempty
    · obtain ⟨p, hp⟩ := hne
      refine ⟨fun a => (k - a.card) * (a.filter (p < ·)).card, fun _ => 0, ?_⟩
      intro a b ha hb hk
      rw [crossCount_dropped_connected hJ hp a b ha hb]
      simp [← hk]
    · refine ⟨fun _ => 0, fun _ => 0, ?_⟩
      intro a b _ hb _
      have he : b = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i hi => hne ⟨i, hb hi⟩
      simp [he, crossCount]

private theorem sign_pow_mul_star (m : ℕ) :
    (-1 : ℂ) ^ m * star ((-1 : ℂ) ^ m) = 1 := by
  rw [star_pow]
  simp [← mul_pow]

/-- For fixed total occupation, multiplying amplitudes by the cross-inversion sign
at a cut without alternation changes the reduced matrix by a diagonal unitary.
The row and column labels encode subsets of the two sides of the cut. -/
private theorem reduced_matrix_phase
    {I : Set ι} (h : ¬ Alternates I) {A B : Type*} [Fintype B]
    (a : A → Finset ι) (b : B → Finset ι)
    (ha : ∀ x, (↑(a x) : Set ι) ⊆ I) (hb : ∀ y, (↑(b y) : Set ι) ⊆ Iᶜ)
    (k : ℕ) (ψ : A → B → ℂ)
    (hsupp : ∀ x y, (a x).card + (b y).card ≠ k → ψ x y = 0) :
    ∃ d : A → ℂ, (∀ x, d x * star (d x) = 1) ∧
      ∀ x x',
        (∑ y, ((-1 : ℂ) ^ crossCount (a x) (b y) * ψ x y) *
          star ((-1 : ℂ) ^ crossCount (a x') (b y) * ψ x' y)) =
          d x * (∑ y, ψ x y * star (ψ x' y)) * star (d x') := by
  classical
  obtain ⟨l, r, hlr⟩ := phase_factors h k
  let d : A → ℂ := fun x => (-1) ^ l (a x)
  let e : B → ℂ := fun y => (-1) ^ r (b y)
  have hψ (x : A) (y : B) :
      (-1 : ℂ) ^ crossCount (a x) (b y) * ψ x y = d x * (e y * ψ x y) := by
    by_cases hk : (a x).card + (b y).card = k
    · rw [hlr (a x) (b y) (ha x) (hb y) hk, pow_add]
      exact mul_assoc _ _ _
    · simp [hsupp x y hk]
  refine ⟨d, fun x => sign_pow_mul_star (l (a x)), ?_⟩
  intro x x'
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [hψ, hψ, star_mul, star_mul]
  calc
    (d x * (e y * ψ x y)) * (star (ψ x' y) * star (e y) * star (d x')) =
        (e y * star (e y)) * (d x * (ψ x y * star (ψ x' y)) * star (d x')) := by ring
    _ = _ := by rw [show e y * star (e y) = 1 from sign_pow_mul_star (r (b y)), one_mul]

/-- Equality of characteristic polynomials preserves every eigenvalue
with its algebraic multiplicity, including zero. -/
theorem reduction_charpoly
    {I : Set ι} (h : ¬ Alternates I) {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (a : A → Finset ι) (b : B → Finset ι)
    (ha : ∀ x, (↑(a x) : Set ι) ⊆ I) (hb : ∀ y, (↑(b y) : Set ι) ⊆ Iᶜ)
    (k : ℕ) (ψ : Matrix A B ℂ)
    (hsupp : ∀ x y, (a x).card + (b y).card ≠ k → ψ x y = 0) :
    let signed : Matrix A B ℂ := fun x y => (-1) ^ crossCount (a x) (b y) * ψ x y
    (signed * signed.conjTranspose).charpoly = (ψ * ψ.conjTranspose).charpoly := by
  intro signed
  obtain ⟨d, hd, hred⟩ := reduced_matrix_phase h a b ha hb k ψ hsupp
  let D : Matrix A A ℂ := Matrix.diagonal d
  let D' : Matrix A A ℂ := Matrix.diagonal fun x => star (d x)
  have hinv : D' * D = 1 := by
    change Matrix.diagonal (fun x => star (d x)) * Matrix.diagonal d = 1
    rw [Matrix.diagonal_mul_diagonal]
    have he : (fun x => star (d x) * d x) = fun _ => (1 : ℂ) := by
      funext x
      rw [mul_comm, hd x]
    rw [he, Matrix.diagonal_one]
  have hm : signed * signed.conjTranspose = D * (ψ * ψ.conjTranspose) * D' := by
    ext x x'
    change (signed * signed.conjTranspose) x x' =
      (Matrix.diagonal d * (ψ * ψ.conjTranspose) *
        Matrix.diagonal (fun x => star (d x))) x x'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, signed]
    exact hred x x'
  rw [hm, Matrix.charpoly_mul_comm (D * (ψ * ψ.conjTranspose)) D',
    ← Matrix.mul_assoc D' D _, hinv, one_mul]

end D5.S3.Quantum.Fermionic.SlaterCutPhase
