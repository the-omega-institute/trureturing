/- GID: D5/S3/Combinatorics/DihedralRamsey/PathStar
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/PathStar
   mirror-E: none(waiver:dihedral-path-star-ramsey)
   anchors: [mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: The exact dihedral Ramsey number of an alternating path versus a star. -/

import D5.S3.Combinatorics.DihedralRamsey.CyclicRamseyDefs
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyStar
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyExtremal
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyCircular
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyMatching
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.PathStar

open DihedralRamseyDefs CyclicRamseyDefs Finset

/-- A cyclic forcing bound and matching dihedral obstruction for paths versus stars. -/
theorem bounds (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (∀ G : SimpleGraph (Fin (a + b - 2 - a * b % 2)),
      CyclicEmbeddable (altPath a) G ∨ CyclicEmbeddable (startStar b) Gᶜ) ∧
    (∀ l : ℕ, l < a + b - 2 - a * b % 2 →
      ¬∀ G : SimpleGraph (Fin l),
        DihedralEmbeddable (altPath a) G ∨ DihedralEmbeddable (startStar b) Gᶜ) := by
  classical
  let N := a + b - 2 - a * b % 2
  have hp : a * b % 2 ≤ 1 := by omega
  have hN : 0 < N := by dsimp [N]; omega
  have upper : ∀ G : SimpleGraph (Fin N),
      CyclicEmbeddable (altPath a) G ∨ CyclicEmbeddable (startStar b) Gᶜ := by
    intro G
    by_contra h
    replace h := not_or.mp h
    have hA := extremal ha G h.1
    change 2 * G.edgeFinset.card ≤ (a - 2) * N at hA
    have hblue : ∀ v : Fin N, Gᶜ.degree v ≤ b - 2 := by
      intro v
      by_contra hgt
      apply h.2
      apply (star_iff_degree hb false Gᶜ).mpr
      exact ⟨v, by omega⟩
    have hdeg : ∀ v : Fin N, G.degree v + Gᶜ.degree v = N - 1 := by
      intro v
      have hl := G.degree_lt_card_verts v
      rw [G.degree_compl, Fintype.card_fin]
      simp only [Fintype.card_fin] at hl
      omega
    by_cases hpar : a * b % 2 = 0
    · have he : N = a + b - 2 := by simp [N, hpar]
      have hmin : ∀ v : Fin N, a - 1 ≤ G.degree v := by
        intro v
        have hd := hdeg v
        have hb' := hblue v
        omega
      have hs : N * (a - 1) ≤ ∑ v, G.degree v := by
        calc
          N * (a - 1) = ∑ _ : Fin N, (a - 1) := by simp
          _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hmin v
      rw [G.sum_degrees_eq_twice_card_edges] at hs
      have ha' : a - 2 + 2 = a := by omega
      have ha'' : a - 1 + 1 = a := by omega
      nlinarith
    · have hpar' : a * b % 2 = 1 := by omega
      have hpa : a % 2 = 1 := by
        rw [Nat.mul_mod] at hpar'
        rcases Nat.mod_two_eq_zero_or_one a with h | h
        · simp [h] at hpar'
        · exact h
      have hpb : b % 2 = 1 := by
        rw [Nat.mul_mod, hpa] at hpar'
        simpa using hpar'
      have he : N = a + b - 3 := by dsimp [N]; omega
      have hmin : ∀ v : Fin N, a - 2 ≤ G.degree v := by
        intro v
        have hd := hdeg v
        have hb' := hblue v
        omega
      have hs : N * (a - 2) ≤ ∑ v, G.degree v := by
        calc
          N * (a - 2) = ∑ _ : Fin N, (a - 2) := by simp
          _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hmin v
      rw [G.sum_degrees_eq_twice_card_edges] at hs
      have hsum : 2 * G.edgeFinset.card = (a - 2) * N := by
        exact le_antisymm hA (by simpa only [Nat.mul_comm N] using hs)
      have hNodd : N % 2 = 1 := by omega
      have hpa' : (a - 2) % 2 = 1 := by omega
      have hprod : ((a - 2) * N) % 2 = 1 := by
        simp [Nat.mul_mod, hpa', hNodd]
      have hmod := congrArg (fun x => x % 2) hsum
      omega
  -- Circular colourings attain the host order immediately below the upper bound.
  let m := N - 1
  have lower : ∃ G : SimpleGraph (Fin m),
      ¬DihedralEmbeddable (altPath a) G ∧ ¬DihedralEmbeddable (startStar b) Gᶜ := by
    by_cases hpa : a % 2 = 0
    · let r := (a - 2) / 2
      have har : a = 2 * r + 2 := by dsimp [r]; omega
      have hpar : a * b % 2 = 0 := by simp [Nat.mul_mod, hpa]
      have hm : m = 2 * r + b - 1 := by dsimp [m, N]; omega
      obtain ⟨G, hG, hD, _⟩ := short_circular_colouring
        (a := a) (n := m) (r := r) (by omega) (by omega)
      refine ⟨G, hG, ?_⟩
      rintro hE
      obtain ⟨s, refl, ψ, hψ, he⟩ := hE
      obtain ⟨v, hv⟩ := (star_iff_degree hb refl Gᶜ).mp ⟨s, ψ, hψ, he⟩
      have hdeg : Gᶜ.degree v ≤ m - 2 * r - 1 := by
        convert hD v using 1
        exact congrArg (fun I : Fintype (Gᶜ.neighborSet v) => @SimpleGraph.degree _ Gᶜ v I)
          (Subsingleton.elim _ _)
      omega
    · have haodd : a % 2 = 1 := by omega
      have ha3 : 3 ≤ a := by omega
      let r := (a - 3) / 2
      have har : a = 2 * r + 3 := by dsimp [r]; omega
      by_cases hpb : b % 2 = 0
      · have hpar : a * b % 2 = 0 := by simp [Nat.mul_mod, hpb]
        have hm : m = 2 * r + b := by dsimp [m, N]; omega
        have hmeven : m % 2 = 0 := by omega
        obtain ⟨G, hG, hD⟩ := antipodal_circular_colouring (n := m) (r := r)
          hmeven (by omega)
        refine ⟨G, ?_, ?_⟩
        · rw [har]
          exact hG
        · intro hE
          obtain ⟨s, refl, ψ, hψ, he⟩ := hE
          obtain ⟨v, hv⟩ := (star_iff_degree hb refl Gᶜ).mp ⟨s, ψ, hψ, he⟩
          have hdeg : Gᶜ.degree v ≤ m - 2 * r - 2 := by
            convert hD v using 1
            exact congrArg
              (fun I : Fintype (Gᶜ.neighborSet v) => @SimpleGraph.degree _ Gᶜ v I)
              (Subsingleton.elim _ _)
          omega
      · have hbodd : b % 2 = 1 := by omega
        have hpar : a * b % 2 = 1 := by simp [Nat.mul_mod, haodd, hbodd]
        have hm : m = 2 * r + b - 1 := by dsimp [m, N]; omega
        obtain ⟨G, hG, hD, _⟩ := short_circular_colouring
          (a := a) (n := m) (r := r) (by omega) (by omega)
        refine ⟨G, hG, ?_⟩
        intro hE
        obtain ⟨s, refl, ψ, hψ, he⟩ := hE
        obtain ⟨v, hv⟩ := (star_iff_degree hb refl Gᶜ).mp ⟨s, ψ, hψ, he⟩
        have hdeg : Gᶜ.degree v ≤ m - 2 * r - 1 := by
          convert hD v using 1
          exact congrArg
            (fun I : Fintype (Gᶜ.neighborSet v) => @SimpleGraph.degree _ Gᶜ v I)
            (Subsingleton.elim _ _)
        omega
  obtain ⟨G, hred, hblue⟩ := lower
  have smaller : ∀ l : ℕ, l < N → ¬∀ H : SimpleGraph (Fin l),
      DihedralEmbeddable (altPath a) H ∨ DihedralEmbeddable (startStar b) Hᶜ := by
    intro l hl hforce
    have hlm : l ≤ m := by dsimp [m]; omega
    let e := Fin.castLEOrderEmb hlm
    let H := G.comap e
    have lift : ∀ {k : ℕ} (J : SimpleGraph (Fin k)),
        DihedralEmbeddable J H → DihedralEmbeddable J G := by
      intro k J hJ
      obtain ⟨s, refl, ψ, hψ, hE⟩ := hJ
      exact ⟨s, refl, e ∘ ψ, e.strictMono.comp hψ, hE⟩
    have liftblue : DihedralEmbeddable (startStar b) Hᶜ →
        DihedralEmbeddable (startStar b) Gᶜ := by
      rintro ⟨s, refl, ψ, hψ, hE⟩
      refine ⟨s, refl, e ∘ ψ, e.strictMono.comp hψ, ?_⟩
      intro i j hij
      have he := hE i j hij
      change _ ≠ _ ∧ ¬G.Adj _ _ at he ⊢
      exact ⟨fun h => he.1 (e.injective h), he.2⟩
    rcases hforce H with h | h
    · exact hred (lift _ h)
    · exact hblue (liftblue h)
  exact ⟨upper, smaller⟩

/-- Conjecture 4.5, including both parity cases and every smaller host order. -/
theorem result : DihedralRamseyDefs.claimPathStar := by
  intro a b ha hb
  obtain ⟨upper, smaller⟩ := bounds a b ha hb
  let N := a + b - 2 - a * b % 2
  have upper' : ∀ G : SimpleGraph (Fin N),
      DihedralEmbeddable (altPath a) G ∨ DihedralEmbeddable (startStar b) Gᶜ := by
    intro G
    rcases upper G with ⟨s, ψ, hψ, he⟩ | ⟨s, ψ, hψ, he⟩
    · exact Or.inl ⟨s, false, ψ, hψ, he⟩
    · exact Or.inr ⟨s, false, ψ, hψ, he⟩
  let S : Set ℕ := {l | ∀ H : SimpleGraph (Fin l),
    DihedralEmbeddable (altPath a) H ∨ DihedralEmbeddable (startStar b) Hᶜ}
  change sInf S = N
  apply le_antisymm
  · exact Nat.sInf_le (show N ∈ S from upper')
  · have hm := Nat.sInf_mem (show S.Nonempty from ⟨N, upper'⟩)
    by_contra hlt
    exact smaller _ (by omega) hm

end D5.S3.Combinatorics.DihedralRamsey.PathStar
