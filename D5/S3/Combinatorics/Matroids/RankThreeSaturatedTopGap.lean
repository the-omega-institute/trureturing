/- GID: D5/S3/Combinatorics/Matroids/RankThreeSaturatedTopGap
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeSaturatedTopGap
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Top gaps in saturated ternary internal extensions arise from six-cycle leaves of Steiner packings. -/

import D5.S3.Combinatorics.Matroids.RankThreeInternalSizeSpectrum

/-! # The top gap for saturated internal extensions -/

namespace D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap

open Set
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)

private def Covered {r : ℕ} (P : Set (Set (Fin r))) (a b : Fin r) : Prop :=
  ∃ s ∈ P, a ∈ s ∧ b ∈ s

private def Complete {r : ℕ} (P : Set (Set (Fin r))) : Prop :=
  ∀ a b, a ≠ b → Covered P a b

private def Maximal {r : ℕ} (P : Set (Set (Fin r))) : Prop :=
  ∀ Q, IsPartialSteiner Q → P ⊆ Q → Q = P

private theorem pair_completion {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) {a b : Fin r} (ne : a ≠ b) (covered : Covered P a b) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ ({a, b, x} : Set (Fin r)) ∈ P := by
  obtain ⟨s, hs, ha, hb⟩ := covered
  have outside : ∃ x ∈ s, x ∉ ({a, b} : Set (Fin r)) := by
    by_contra! no
    have upper := Set.ncard_le_ncard (show s ⊆ {a, b} from no)
    rw [valid.1 s hs, Set.ncard_pair ne] at upper
    omega
  obtain ⟨x, hx, hne⟩ := outside
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
  have sub : ({a, b, x} : Set (Fin r)) ⊆ s := by
    simpa only [insert_subset_iff, singleton_subset_iff] using And.intro ha (And.intro hb hx)
  have card : ({a, b, x} : Set (Fin r)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, x, ne, hne.1.symm, hne.2.symm, rfl⟩
  have eq := Set.eq_of_subset_of_ncard_le sub (by rw [valid.1 s hs, card])
  exact ⟨x, hne.1, hne.2, eq.symm ▸ hs⟩

private theorem maximal_of_no_uncovered_triple {r : ℕ} {P : Set (Set (Fin r))}
    (test : ∀ a b c, a ≠ b → b ≠ c → c ≠ a →
      Covered P a b ∨ Covered P b c ∨ Covered P c a) :
    Maximal P := by
  intro Q hQ sub
  apply Subset.antisymm _ sub
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.mp (hQ.1 s hs)
  have transfer (u v : Fin r) (ne : u ≠ v) (hu : u ∈ ({a,b,c} : Set (Fin r)))
      (hv : v ∈ ({a,b,c} : Set (Fin r))) (cov : Covered P u v) :
      ({a,b,c} : Set (Fin r)) ∈ P := by
    obtain ⟨t, ht, htu, htv⟩ := cov
    have eq := hQ.2 _ hs t (sub ht) u v ne hu hv htu htv
    exact eq.symm ▸ ht
  rcases test a b c hab hbc hac.symm with h | h | h
  · exact transfer a b hab (by simp) (by simp) h
  · exact transfer b c hbc (by simp) (by simp) h
  · exact transfer c a hac.symm (by simp) (by simp) h

private theorem swap_at_nonblock {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) (complete : Complete P)
    {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (missing : ({a,b,c} : Set (Fin r)) ∉ P) :
    ∃ Q : Set (Set (Fin r)), IsPartialSteiner Q ∧ Maximal Q ∧ Q.ncard + 2 = P.ncard := by
  classical
  obtain ⟨x, hxa, hxb, hx⟩ := pair_completion valid hab (complete a b hab)
  obtain ⟨y, hyb, hyc, hy⟩ := pair_completion valid hbc (complete b c hbc)
  obtain ⟨z, hzc, hza, hz⟩ := pair_completion valid hca (complete c a hca)
  have hxc : x ≠ c := fun h => missing (by simpa [h] using hx)
  have hya : y ≠ a := by
    intro h
    apply missing
    convert hy using 1
    ext i
    simp only [h, mem_insert_iff, mem_singleton_iff]
    tauto
  have hzb : z ≠ b := by
    intro h
    apply missing
    convert hz using 1
    ext i
    simp only [h, mem_insert_iff, mem_singleton_iff]
    tauto
  let A : Set (Fin r) := {a,b,c}
  let B₀ : Set (Fin r) := {a,b,x}
  let B₁ : Set (Fin r) := {b,c,y}
  let B₂ : Set (Fin r) := {c,a,z}
  let removed : Set (Set (Fin r)) := {B₀,B₁,B₂}
  have h₀₁ : B₀ ≠ B₁ := by
    intro eq
    have mem : a ∈ B₁ := eq ▸ (show a ∈ B₀ by simp [B₀])
    simpa [B₁, hab, hca.symm, hya.symm] using mem
  have h₁₂ : B₁ ≠ B₂ := by
    intro eq
    have mem : b ∈ B₂ := eq ▸ (show b ∈ B₁ by simp [B₁])
    simpa [B₂, hbc, hab.symm, hzb.symm] using mem
  have h₀₂ : B₀ ≠ B₂ := by
    intro eq
    have mem : b ∈ B₂ := eq ▸ (show b ∈ B₀ by simp [B₀])
    simpa [B₂, hbc, hab.symm, hzb.symm] using mem
  have hxy : x ≠ y := by
    intro eq
    exact h₀₁ (valid.2 B₀ hx B₁ hy b x hxb.symm (by simp [B₀]) (by simp [B₀])
      (by simp [B₁]) (by simp [B₁, eq]))
  have hyz : y ≠ z := by
    intro eq
    exact h₁₂ (valid.2 B₁ hy B₂ hz c y hyc.symm (by simp [B₁]) (by simp [B₁])
      (by simp [B₂]) (by simp [B₂, eq]))
  have hzx : z ≠ x := by
    intro eq
    exact h₀₂ ((valid.2 B₂ hz B₀ hx a z hza.symm (by simp [B₂]) (by simp [B₂])
      (by simp [B₀]) (by simp [B₀, eq])).symm)
  let Q := insert A (P \ removed)
  have hremoved : removed ⊆ P := by
    intro s hs
    rcases (show s = B₀ ∨ s = B₁ ∨ s = B₂ by simpa [removed] using hs) with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have old_pair (u v : Fin r) (ne : u ≠ v) (hu : u ∈ A) (hv : v ∈ A) :
      ∃ s ∈ removed, u ∈ s ∧ v ∈ s := by
    simp only [A, mem_insert_iff, mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (ne rfl).elim
    · exact ⟨B₀, by simp [removed], by simp [B₀], by simp [B₀]⟩
    · exact ⟨B₂, by simp [removed], by simp [B₂], by simp [B₂]⟩
    · exact ⟨B₀, by simp [removed], by simp [B₀], by simp [B₀]⟩
    · exact (ne rfl).elim
    · exact ⟨B₁, by simp [removed], by simp [B₁], by simp [B₁]⟩
    · exact ⟨B₂, by simp [removed], by simp [B₂], by simp [B₂]⟩
    · exact ⟨B₁, by simp [removed], by simp [B₁], by simp [B₁]⟩
    · exact (ne rfl).elim
  have no_overlap {u v : Fin r} (ne : u ≠ v) (hu : u ∈ A) (hv : v ∈ A)
      {t : Set (Fin r)} (ht : t ∈ P \ removed) (htu : u ∈ t) (htv : v ∈ t) : False := by
    obtain ⟨s, hs, hsu, hsv⟩ := old_pair u v ne hu hv
    exact ht.2 (valid.2 s (hremoved hs) t ht.1 u v ne hsu hsv htu htv ▸ hs)
  have validQ : IsPartialSteiner Q := by
    constructor
    · intro s hs
      rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs
      · exact Set.ncard_eq_three.mpr ⟨a, b, c, hab, hca.symm, hbc, rfl⟩
      · exact valid.1 s hs.1
    · intro s hs t ht u v ne hsu hsv htu htv
      rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs <;>
        rcases (show t = A ∨ t ∈ P \ removed from ht) with rfl | ht
      · rfl
      · exact (no_overlap ne hsu hsv ht htu htv).elim
      · exact (no_overlap ne htu htv hs hsu hsv).elim
      · exact valid.2 s hs.1 t ht.1 u v ne hsu hsv htu htv
  have leave (u v : Fin r) (ne : u ≠ v) :
      ¬ Covered Q u v ↔
        (u = x ∧ (v = a ∨ v = b)) ∨ (v = x ∧ (u = a ∨ u = b)) ∨
        (u = y ∧ (v = b ∨ v = c)) ∨ (v = y ∧ (u = b ∨ u = c)) ∨
        (u = z ∧ (v = c ∨ v = a)) ∨ (v = z ∧ (u = c ∨ u = a)) := by
    have law : ¬ Covered Q u v ↔
        (¬ (u ∈ A ∧ v ∈ A)) ∧ ∃ t ∈ removed, u ∈ t ∧ v ∈ t := by
      constructor
      · intro unseen
        refine ⟨fun h => unseen ⟨A, by simp [Q], h.1, h.2⟩, ?_⟩
        obtain ⟨s, hs, hu, hv⟩ := complete u v ne
        by_cases h : s ∈ removed
        · exact ⟨s, h, hu, hv⟩
        · exact (unseen ⟨s, Or.inr ⟨hs, h⟩, hu, hv⟩).elim
      · rintro ⟨notBoth, t, ht, htu, htv⟩ ⟨s, hs, hsu, hsv⟩
        rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs
        · exact notBoth ⟨hsu, hsv⟩
        · exact hs.2 (valid.2 t (hremoved ht) s hs.1 u v ne htu htv hsu hsv ▸ ht)
    rw [law]
    have removed_pair :
        (∃ t ∈ removed, u ∈ t ∧ v ∈ t) ↔
          (u ∈ B₀ ∧ v ∈ B₀) ∨ (u ∈ B₁ ∧ v ∈ B₁) ∨ (u ∈ B₂ ∧ v ∈ B₂) := by
      simp [removed, or_and_right]
    rw [removed_pair]
    simp only [A, B₀, B₁, B₂, mem_insert_iff, mem_singleton_iff]
    grind
  have maxQ : Maximal Q := by
    apply maximal_of_no_uncovered_triple
    intro u v w huv hvw hwu
    by_contra! ht
    have p := (leave u v huv).mp ht.1
    have q := (leave v w hvw).mp ht.2.1
    have s := (leave w u hwu).mp ht.2.2
    grind
  have removedCard : removed.ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨B₀, B₁, B₂, h₀₁, h₀₂, h₁₂, rfl⟩
  have missingResidual : A ∉ P \ removed := fun h => missing h.1
  have count := Set.ncard_sdiff_add_ncard_of_subset hremoved
  refine ⟨Q, validQ, maxQ, ?_⟩
  rw [show Q = insert A (P \ removed) from rfl, Set.ncard_insert_of_notMem missingResidual]
  omega

end D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap
