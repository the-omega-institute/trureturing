/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The open supersymmetric M1 chain on hard-core configurations. -/

/-
annihilator_number:
  proof_shape: content
  escape_witness: annihilator_number (form 2): Erasing an occupied site preserves nearest-neighbour exclusion; injectivity on occupied preimages and cancellation of the Jordan–Wigner signs identify c†c with the occupation diagonal at every site.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner; freeze in topological import order.
Reused predicate: D5/S1/Words/AdmissibleWords/AdmissibleCount.Adm.
Pointwise exclusion: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true; sha256:1fd94a32ad20c5e9f47c8843c130133ce27a104e2f7f75cb9bf9916f8085bc2b.
Information-escape registration is paused under CLAUDE.md §3.9.
-/


import D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
import D5.S1.Words.AdmissibleWords.AdmissibleCount
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix Classical
set_option quotPrecheck false in
local notation "tensorOp" => (fun {N : ℕ} (w : Fin N → Matrix Bool Bool ℂ) =>
  Matrix.submatrix
    (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp (n := N)
      (fun i => Matrix.submatrix (w i) finTwoEquiv finTwoEquiv))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i)))
open PredictiveThermodynamic.Physical (Assignment visibleProjector)
open D5.S3.Quantum.FiniteDimensional (qubitZ)
local notation "spinZ" => (qubitZ.submatrix finTwoEquiv.symm finTwoEquiv.symm)
local notation "spinP" => ((1 : Matrix Bool Bool ℂ) - visibleProjector)

namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel
noncomputable section
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner

abbrev HardCore (N : ℕ) := {s : Assignment N // Adm N s}

abbrev HardCoreSpace (N : ℕ) := EuclideanSpace ℂ (HardCore N)

abbrev Operator (N : ℕ) := Matrix (HardCore N) (HardCore N) ℂ

def occupied {N : ℕ} (s : Assignment N) (j : ℕ) : Bool :=
  if h : 0 < j ∧ j ≤ N then s ⟨j - 1, by omega⟩ else false

def annihilationAt {N : ℕ} (i : Fin N) : Operator N := fun s t =>
  if t.val i = true ∧ s.val = Function.update t.val i false
  then (-1 : ℂ) ^ prefixCount t.val i else 0

def c {N : ℕ} (j : ℕ) : Operator N :=
  if h : 0 < j ∧ j ≤ N then annihilationAt ⟨j - 1, by omega⟩ else 0

def number {N : ℕ} (j : ℕ) : Operator N :=
  Matrix.diagonal fun s => if occupied s.val j then 1 else 0

def P {N : ℕ} (j : ℕ) : Operator N := 1 - number j

def d {N : ℕ} (j : ℕ) : Operator N := P (j - 1) * c j * P (j + 1)

def periodThree (a b cc : ℝ) (j : ℕ) : ℝ :=
  if j % 3 = 1 then a else if j % 3 = 2 then b else cc

def stagII (y : ℝ) : ℕ → ℝ := periodThree y y 1

def Qmat (N : ℕ) (coupling : ℕ → ℝ) : Operator N :=
  ∑ j ∈ Finset.range N, (coupling (j + 1) : ℂ) • d (j + 1)

def Q (N : ℕ) (coupling : ℕ → ℝ) := Matrix.toEuclideanLin (Qmat N coupling)

def H (N : ℕ) (coupling : ℕ → ℝ) :
    HardCoreSpace N →ₗ[ℂ] HardCoreSpace N :=
  Q N coupling * (Q N coupling).adjoint + (Q N coupling).adjoint * Q N coupling

def density {N : ℕ} (j : ℕ) (ψ : HardCoreSpace N) : ℂ :=
  inner ℂ ψ (Matrix.toEuclideanLin (number j) ψ) / inner ℂ ψ ψ

def Rmat (N : ℕ) (a b cc : ℝ) : Operator N :=
  (a * cc ^ 2 : ℝ) • (d 1)ᴴ - (a ^ 2 * cc : ℝ) • (d N)ᴴ +
  (∑ k ∈ Finset.range (N - 2),
    let j := k + 3
    (periodThree a b cc j * periodThree a b cc (j - 1) ^ 2 : ℝ) •
      (number (j - 2) * (d j)ᴴ)) -
  (∑ k ∈ Finset.range (N - 2),
    let j := k + 1
    (periodThree a b cc j * periodThree a b cc (j + 1) ^ 2 : ℝ) •
      (number (j + 2) * (d j)ᴴ)) +
  (a * b * cc : ℝ) •
    (∑ k ∈ Finset.range (N - 2),
      let j := k + 1
      P (j - 1) * (c j)ᴴ * (c (j + 2))ᴴ * c (j + 1) * P (j + 3))

private def erase {N : ℕ} (t : HardCore N) (j : Fin N) : HardCore N := by
  have adjacent_iff {M : ℕ} (s : Assignment M) :
      Adm M s ↔ ∀ i k : Fin M, i.val + 1 = k.val → s i = true → s k = false := by
    simp only [adm_iff_no_adjacent_true, or_iff_not_imp_left, Bool.eq_true_eq_not_eq_false]
  have erase_is_hard_core {N : ℕ} (t : HardCore N) (j : Fin N) :
      Adm N (Function.update t.val j false) := by
    rw [adjacent_iff]
    intro i k hik hi
    by_cases hij : i = j
    · subst i
      simp at hi
    by_cases hkj : k = j
    · subst k
      simp
    · simpa only [Function.update_of_ne hkj] using
        (((adjacent_iff t.val).mp t.property) i k hik (by simpa only [Function.update_of_ne hij] using hi))
  exact   ⟨Function.update t.val j false, erase_is_hard_core t j⟩

theorem annihilator_number {N : ℕ} (j : ℕ) :
    (c (N := N) j)ᴴ * c j = number j := by
  have at_number (i : Fin N) :
      (annihilationAt i)ᴴ * annihilationAt i =
        Matrix.diagonal (fun s : HardCore N => if s.val i then (1 : ℂ) else 0) := by
    have erased_config_injective {N : ℕ} (s t : HardCore N) (i : Fin N)
        (hs : s.val i = true) (ht : t.val i = true)
        (he : (erase s i).val = (erase t i).val) : s = t := by
      apply Subtype.ext
      funext k
      by_cases hk : k = i
      · subst k
        exact hs.trans ht.symm
      · have h := congrFun he k
        simpa only [erase, Function.update_of_ne hk] using h
    classical
    ext s t
    rw [Matrix.mul_apply]
    by_cases hs : s.val i = true
    · by_cases ht : t.val i = true
      · rw [Finset.sum_eq_single (erase t i)]
        · by_cases hst : s = t
          · subst s
            simp only [Matrix.conjTranspose_apply, annihilationAt, ht, true_and,
              erase, if_pos rfl, Matrix.diagonal_apply_eq, ite_true]
            simp only [star_pow, star_neg, star_one]
            rw [← mul_pow]
            simp
          · have hne : (erase t i).val ≠ Function.update s.val i false := by
              intro hh
              exact hst (erased_config_injective s t i hs ht hh.symm)
            simp [Matrix.conjTranspose_apply, annihilationAt, hs, ht,
              hne, Matrix.diagonal_apply, hst]
        · intro u _hu hut
          have hne : u.val ≠ Function.update t.val i false := by
            intro hh
            exact hut (Subtype.ext hh)
          simp [annihilationAt, ht, hne]
        · simp
      · have hst : s ≠ t := by intro hh; subst t; exact ht hs
        simp [Matrix.conjTranspose_apply, annihilationAt, ht,
          Matrix.diagonal_apply, hst]
    · simp [Matrix.conjTranspose_apply, annihilationAt, hs, Matrix.diagonal_apply]
  by_cases hj : 0 < j ∧ j ≤ N
  · simpa [c, number, occupied, hj] using at_number ⟨j - 1, by omega⟩
  · simp [c, number, occupied, hj]

end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel
