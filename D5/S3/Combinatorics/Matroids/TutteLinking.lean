/- GID: D5/S3/Combinatorics/Matroids/TutteLinking
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/TutteLinking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An actual terminal minor attains the finite Tutte cut minimum. -/

module

public import D5.S3.Combinatorics.Matroids.FiniteIntersection
public import Mathlib.Tactic.TautoSet

/-! # Finite Tutte linking

The classical finite linking theorem is Theorem 1 of Bruhn and Wollan,
*Finite connectivity in infinite matroids*, arXiv:1101.5621v1, pp. 1–2.
-/

@[expose] public section

open Set Matroid
open D5.S3.Combinatorics.Matroids.FiniteIntersection

namespace D5.S3.Combinatorics.Matroids.TutteLinking

universe u

/-- Natural rank; finiteness of the carrier prevents loss at infinity. -/
noncomputable def rk {E : Type u} (M : Matroid E) (X : Set E) : ℕ :=
  (M.eRk X).toNat

/-- Connectivity of a cut, with complement relative to the matroid ground. -/
noncomputable def cut {E : Type u} (M : Matroid E) (X : Set E) : ℕ :=
  rk M X + rk M (M.E \ X) - rk M M.E

/-- The minimum connectivity of a cut separating the two terminal sets. -/
noncomputable def kappa {E : Type u} (M : Matroid E) (S T : Set E) : ℕ :=
  sInf {n : ℕ | ∃ X : Set E, S ⊆ X ∧ X ⊆ M.E \ T ∧ cut M X = n}

set_option maxHeartbeats 2000000 in
/-- Tutte linking on every finite native matroid, including empty terminal sets. -/
theorem tutte_linking (E : Type u) [Finite E] (M : Matroid E) (S T : Set E)
    (hS : S ⊆ M.E) (hT : T ⊆ M.E) (hST : Disjoint S T) :
    ∃ C : Set E, C ⊆ M.E \ (S ∪ T) ∧
      let D : Set E := (M.E \ (S ∪ T)) \ C
      let N : Matroid E := (M ／ C) ＼ D
      N.E = S ∪ T ∧ rk N S + rk N T - rk N (S ∪ T) = kappa M S T := by
  classical
  let R := M.E \ (S ∪ T)
  let A := (M ／ S) ＼ T
  let B := (M ／ T) ＼ S
  have hAE : A.E = R := by change (M.E \ S) \ T = M.E \ (S ∪ T); tauto_set
  have hBE : B.E = R := by change (M.E \ T) \ S = M.E \ (S ∪ T); tauto_set
  obtain ⟨⟨I, X, hIR, hXR, hIA, hIB, hIX⟩, hupper⟩ :=
    finite_matroid_intersection R (Set.toFinite R) A B hAE hBE
  have hIS : (M ／ S).Indep I := hIA.of_delete
  have hIT : (M ／ T).Indep I := hIB.of_delete
  have hI : M.Indep I := hIS.of_contract
  have hcontract (C Z : Set E) : rk (M ／ C) Z + rk M C = rk M (Z ∪ C) := by
    apply ENat.natCast_inj.mp
    simpa only [Nat.cast_add, rk, cast_toNat_eRk] using contract_eRk_add M C Z
  have hArank (Z : Set E) (hZ : Z ⊆ R) : rk A Z + rk M S = rk M (Z ∪ S) := by
    have hz : Z ⊆ (M ／ S).E \ T := by
      dsimp [R] at hZ
      simp only [contract_ground]
      clear * - hZ
      tauto_set
    dsimp [A, rk]
    rw [← restrict_compl, restrict_eRk_eq _ hz]
    exact hcontract S Z
  have hBrank (Z : Set E) (hZ : Z ⊆ R) : rk B Z + rk M T = rk M (Z ∪ T) := by
    have hz : Z ⊆ (M ／ T).E \ S := by
      dsimp [R] at hZ
      simp only [contract_ground]
      clear * - hZ
      tauto_set
    dsimp [B, rk]
    rw [← restrict_compl, restrict_eRk_eq _ hz]
    exact hcontract T Z
  have hspan : M.Spanning ((S ∪ T) ∪ I) := by
    rw [spanning_iff_ground_subset_closure (union_subset (union_subset hS hT) hI.subset_ground)]
    intro e he
    by_contra hn
    have heI : e ∉ I := fun hi => hn (M.mem_closure_of_mem' (Or.inr hi) he)
    have heS : e ∉ S := fun hs => hn (M.mem_closure_of_mem' (Or.inl (Or.inl hs)) he)
    have heT : e ∉ T := fun ht => hn (M.mem_closure_of_mem' (Or.inl (Or.inr ht)) he)
    have hinsertS : (M ／ S).Indep (insert e I) := by
      apply hIS.insert_indep_iff.mpr
      left
      refine ⟨⟨he, heS⟩, ?_⟩
      rw [contract_closure_eq]
      intro hc
      exact hn (M.closure_mono (by clear * -; tauto_set) hc.1)
    have hinsertT : (M ／ T).Indep (insert e I) := by
      apply hIT.insert_indep_iff.mpr
      left
      refine ⟨⟨he, heT⟩, ?_⟩
      rw [contract_closure_eq]
      intro hc
      exact hn (M.closure_mono (by clear * -; tauto_set) hc.1)
    have hiA : A.Indep (insert e I) := delete_indep_iff.mpr ⟨hinsertS, by
      rw [disjoint_insert_left]
      exact ⟨heT, disjoint_left.mpr (fun x hx ht => (hIR hx).2 (Or.inr ht))⟩⟩
    have hiB : B.Indep (insert e I) := delete_indep_iff.mpr ⟨hinsertT, by
      rw [disjoint_insert_left]
      exact ⟨heS, disjoint_left.mpr (fun x hx hs => (hIR hx).2 (Or.inl hs))⟩⟩
    have hu := hupper (insert e I) X hiA hiB
    rw [ncard_insert_of_notMem heI (Set.toFinite I), ← hIX] at hu
    omega
  have hspanrank : rk M ((S ∪ T) ∪ I) = rk M M.E := by
    unfold rk
    rw [hspan.eRk_eq, eRank_def]
  have hrI : rk M I = I.ncard := by simp only [rk, hI.eRk_eq_encard, ncard_def]
  have hrIS : rk (M ／ S) I = I.ncard := by simp only [rk, hIS.eRk_eq_encard, ncard_def]
  have hrIT : rk (M ／ T) I = I.ncard := by simp only [rk, hIT.eRk_eq_encard, ncard_def]
  let D := R \ I
  let N := (M ／ I) ＼ D
  have hNE : N.E = S ∪ T := by
    change (M.E \ I) \ ((M.E \ (S ∪ T)) \ I) = S ∪ T
    dsimp [R] at hIR
    clear * - hS hT hIR
    tauto_set
  have hNrank (Z : Set E) (hZ : Z ⊆ S ∪ T) : rk N Z = rk (M ／ I) Z := by
    have hz : Z ⊆ (M ／ I).E \ D := by change Z ⊆ N.E; rwa [hNE]
    dsimp [N, rk]
    rw [← restrict_compl, restrict_eRk_eq _ hz]
  have hNS : rk N S = rk M S := by
    have h₁ := hcontract S I
    have h₂ := hcontract I S
    rw [hrIS] at h₁
    rw [← hNrank S subset_union_left, hrI, union_comm S I] at h₂
    omega
  have hNT : rk N T = rk M T := by
    have h₁ := hcontract T I
    have h₂ := hcontract I T
    rw [hrIT] at h₁
    rw [← hNrank T subset_union_right, hrI, union_comm T I] at h₂
    omega
  have hNST : rk N (S ∪ T) + I.ncard = rk M M.E := by
    rw [hNrank _ subset_rfl, ← hrI, hcontract, hspanrank]
  have hcutX : cut M (S ∪ X) = rk N S + rk N T - rk N (S ∪ T) := by
    have hc : M.E \ (S ∪ X) = (R \ X) ∪ T := by dsimp [R] at hXR ⊢; clear * - hS hT hST hXR; tauto_set
    have ha := hArank X hXR
    have hb := hBrank (R \ X) sdiff_subset
    change I.ncard = rk A X + rk B (R \ X) at hIX
    rw [union_comm X S] at ha
    unfold cut
    rw [hc, hNS, hNT]
    omega
  have hfeasible : S ∪ X ⊆ M.E \ T := by dsimp [R] at hXR; clear * - hS hST hXR; tauto_set
  have hlower (Y : Set E) (hSY : S ⊆ Y) (hY : Y ⊆ M.E \ T) :
      rk N S + rk N T - rk N (S ∪ T) ≤ cut M Y := by
    let Z := Y \ S
    have hZR : Z ⊆ R := by dsimp [Z, R]; clear * - hY; tauto_set
    have hZS : Z ∪ S = Y := by dsimp [Z]; clear * - hSY; tauto_set
    have hZT : (R \ Z) ∪ T = M.E \ Y := by dsimp [R, Z]; clear * - hSY hY hS hT hST; tauto_set
    have ha := hArank Z hZR
    have hb := hBrank (R \ Z) sdiff_subset
    have hu := hupper I Z hIA hIB
    change I.ncard ≤ rk A Z + rk B (R \ Z) at hu
    rw [hZS] at ha
    rw [hZT] at hb
    unfold cut
    rw [hNS, hNT]
    omega
  have hattain : cut M (S ∪ X) ∈
      {n : ℕ | ∃ Y : Set E, S ⊆ Y ∧ Y ⊆ M.E \ T ∧ cut M Y = n} :=
    ⟨S ∪ X, subset_union_left, hfeasible, rfl⟩
  refine ⟨I, hIR, hNE, ?_⟩
  apply le_antisymm
  · apply le_csInf
    · exact ⟨cut M (S ∪ X), S ∪ X, subset_union_left, hfeasible, rfl⟩
    · rintro n ⟨Y, hSY, hY, rfl⟩
      exact hlower Y hSY hY
  · exact (csInf_le (OrderBot.bddBelow _) hattain).trans_eq hcutX

#print axioms tutte_linking

end D5.S3.Combinatorics.Matroids.TutteLinking
