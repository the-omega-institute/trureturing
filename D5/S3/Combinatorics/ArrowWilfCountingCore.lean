/- GID: D5/S3/Combinatorics/ArrowWilfCountingCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfCountingCore
   mirror-E: none(waiver:finite-counting-core-for-foata-fixed-points)
   anchors: [mathlib/module/Mathlib.Combinatorics.Derangements.Finite]
   utility: none
   digest: Prescribed Foata fixed points are counted by deleting their singleton blocks. -/

import D5.S3.Combinatorics.ArrowWilfFixedInsertion
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfCountingCore

noncomputable section

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfFixedInsertion

/-- The finite collection of one-line words permuting a finite set. -/
def words (s : Finset ℕ) : Finset (List ℕ) := s.toList.permutations.toFinset

/-- A one-line word whose entries are exactly the elements of `s`. -/
abbrev Word (s : Finset ℕ) := ↑(words s)

/-- Add one new value to the support of a word by canonical fixed-point insertion. -/
def insertWord (s : Finset ℕ) (f : ℕ) (hf : f ∉ s) (p : Word s) : Word (insert f s) := by
  refine ⟨fixedInsert f p.1, ?_⟩
  change fixedInsert f p.1 ∈ words (insert f s)
  rw [words, List.mem_toFinset, List.mem_permutations]
  have hp : p.1.Perm s.toList := by
    simpa [words, List.mem_permutations] using p.2
  have hfn : f ∉ s.toList := by simpa using hf
  apply (fixedInsert_perm f p.1).trans
  apply (hp.cons f).trans
  apply (List.perm_ext_iff_of_nodup (s.nodup_toList.cons hfn)
    (insert f s).nodup_toList).mpr
  intro a
  simp

/-- Delete a prescribed entry from a word. -/
def eraseWord (s : Finset ℕ) (f : ℕ) (p : Word s) : Word (s.erase f) := by
  refine ⟨p.1.erase f, ?_⟩
  change p.1.erase f ∈ words (s.erase f)
  rw [words, List.mem_toFinset, List.mem_permutations]
  have hp : p.1.Perm s.toList := by
    simpa [words, List.mem_permutations] using p.2
  have hperm := hp.erase f
  apply hperm.trans
  apply (List.perm_ext_iff_of_nodup (s.nodup_toList.erase f)
    (s.erase f).nodup_toList).mpr
  intro a
  rw [s.nodup_toList.mem_erase_iff]
  simp [eq_comm]

/-- Canonical insertion is a bijection onto words in which the new value is fixed by `hat`. -/
def fixedWordEquiv (s : Finset ℕ) (f : ℕ) (hf : f ∉ s) :
    Word s ≃ {p : Word (insert f s) // hat p.1 f = f} where
  toFun p := ⟨insertWord s f hf p, by
    have hp : p.1.Nodup := by
      have : p.1.Perm s.toList := by simpa [words, List.mem_permutations] using p.2
      exact this.nodup_iff.mpr s.nodup_toList
    have hfnot : f ∉ p.1 := by
      intro h
      have hperm : p.1.Perm s.toList := by simpa [words, List.mem_permutations] using p.2
      exact hf (by simpa using hperm.mem_iff.mp h)
    have hfmem : f ∈ fixedInsert f p.1 := (fixedInsert_perm f p.1).mem_iff.mpr (by simp)
    have hinsNodup : (fixedInsert f p.1).Nodup :=
      (fixedInsert_perm f p.1).nodup_iff.mpr (by simp [hp, hfnot])
    exact (fixedInsert_erase_eq_iff_hat_fixed hinsNodup hfmem).mp
      (congrArg (fixedInsert f) (erase_fixedInsert hfnot))⟩
  invFun p := by
    refine ⟨p.1.1.erase f, ?_⟩
    change p.1.1.erase f ∈ words s
    rw [words, List.mem_toFinset, List.mem_permutations]
    have hpperm : p.1.1.Perm (insert f s).toList := by
      simpa [words, List.mem_permutations] using p.1.2
    apply (hpperm.erase f).trans
    apply (List.perm_ext_iff_of_nodup ((insert f s).nodup_toList.erase f)
      s.nodup_toList).mpr
    intro a
    rw [(insert f s).nodup_toList.mem_erase_iff]
    simp only [Finset.mem_toList, Finset.mem_insert]
    constructor
    · rintro ⟨hne, h | h⟩
      · exact (hne h).elim
      · exact h
    · intro ha
      exact ⟨by rintro rfl; exact hf ha, Or.inr ha⟩
  left_inv p := by
    apply Subtype.ext
    exact erase_fixedInsert (by
      intro h
      have hperm : p.1.Perm s.toList := by simpa [words, List.mem_permutations] using p.2
      exact hf (by simpa using hperm.mem_iff.mp h))
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    have hpNodup : p.1.1.Nodup := by
      have hperm : p.1.1.Perm (insert f s).toList := by
        simpa [words, List.mem_permutations] using p.1.2
      exact hperm.nodup_iff.mpr (insert f s).nodup_toList
    have hfmem : f ∈ p.1.1 := by
      have hperm : p.1.1.Perm (insert f s).toList := by
        simpa [words, List.mem_permutations] using p.1.2
      exact hperm.mem_iff.mpr (by simp)
    exact (fixedInsert_erase_eq_iff_hat_fixed hpNodup hfmem).mpr p.2

/-- Words on `s` for which every member of `F` is a fixed point. -/
abbrev ForcedFixed (s F : Finset ℕ) := {p : Word s // ∀ f ∈ F, hat p.1 f = f}

/-- Inserting a fresh fixed point is a bijection after retaining any prescribed old fixed points. -/
def forcedInsertEquiv (s F : Finset ℕ) (f : ℕ) (hf : f ∉ s) (hFs : F ⊆ s) :
    ForcedFixed s F ≃ ForcedFixed (insert f s) (insert f F) where
  toFun p := ⟨insertWord s f hf p.1, by
    intro g hg
    rcases Finset.mem_insert.mp hg with hgf | hgF
    · subst g
      exact (fixedWordEquiv s f hf p.1).2
    · have hpperm : p.1.1.Perm s.toList := by
        simpa [words, List.mem_permutations] using p.1.2
      have hpNodup : p.1.1.Nodup := hpperm.nodup_iff.mpr s.nodup_toList
      have hgf : g ≠ f := by
        intro h
        subst g
        exact hf (hFs hgF)
      have hgmem : g ∈ p.1.1 := hpperm.mem_iff.mpr (by simpa using hFs hgF)
      exact (hat_fixed_fixedInsert_iff hpNodup (by
        intro hmem
        exact hf (by simpa using hpperm.mem_iff.mp hmem)) hgmem hgf.symm).mpr (p.2 g hgF)⟩
  invFun p := by
    let pf : {q : Word (insert f s) // hat q.1 f = f} :=
      ⟨p.1, p.2 f (Finset.mem_insert_self f F)⟩
    let q : Word s := (fixedWordEquiv s f hf).symm pf
    refine ⟨q, ?_⟩
    intro g hgF
    have hgS : g ∈ s := hFs hgF
    have hgf : g ≠ f := by rintro rfl; exact hf hgS
    have hqperm : q.1.Perm s.toList := by
      simpa [words, List.mem_permutations] using q.2
    have hqNodup : q.1.Nodup := hqperm.nodup_iff.mpr s.nodup_toList
    have hgmem : g ∈ q.1 := hqperm.mem_iff.mpr (by simpa using hgS)
    have heq := (fixedWordEquiv s f hf).apply_symm_apply pf
    have hlists : fixedInsert f q.1 = p.1.1 := congrArg (fun z => z.1.1) heq
    apply (hat_fixed_fixedInsert_iff hqNodup (by
      intro hmem
      exact hf (by simpa using hqperm.mem_iff.mp hmem)) hgmem hgf.symm).mp
    rw [hlists]
    exact p.2 g (Finset.mem_insert_of_mem hgF)
  left_inv p := by
    apply Subtype.ext
    change (fixedWordEquiv s f hf).symm ((fixedWordEquiv s f hf) p.1) = p.1
    exact (fixedWordEquiv s f hf).symm_apply_apply p.1
  right_inv p := by
    apply Subtype.ext
    let pf : {q : Word (insert f s) // hat q.1 f = f} :=
      ⟨p.1, p.2 f (Finset.mem_insert_self f F)⟩
    change insertWord s f hf ((fixedWordEquiv s f hf).symm pf) = p.1
    exact congrArg Subtype.val ((fixedWordEquiv s f hf).apply_symm_apply pf)

/-- Prescribing `F` as fixed points leaves an arbitrary permutation of the other entries. -/
theorem card_forcedFixed {s F : Finset ℕ} (hFs : F ⊆ s) :
    Fintype.card (ForcedFixed s F) = (s.card - F.card).factorial := by
  induction F using Finset.induction generalizing s with
  | empty =>
      have hcard : Fintype.card (Word s) = s.card.factorial := by
        rw [Fintype.card_coe]
        change (words s).card = s.card.factorial
        unfold words
        rw [List.toFinset_card_of_nodup (List.nodup_permutations _ s.nodup_toList)]
        simp [List.length_permutations]
      simpa [ForcedFixed] using hcard
  | @insert f F hfF ih =>
      have hfs : f ∈ s := hFs (Finset.mem_insert_self f F)
      have hFsub : F ⊆ s.erase f := by
        intro g hg
        exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hfF hg, hFs (Finset.mem_insert_of_mem hg)⟩
      have he := forcedInsertEquiv (s.erase f) F f (by simp) hFsub
      have hcard := Fintype.card_congr he
      rw [Finset.insert_erase hfs] at hcard
      rw [← hcard, ih hFsub]
      congr 1
      rw [Finset.card_erase_of_mem hfs, Finset.card_insert_of_notMem hfF]
      omega

/-- Words with no `hat`-fixed entry. -/
abbrev NoFixed (s : Finset ℕ) := {p : Word s // ∀ f ∈ s, hat p.1 f ≠ f}

/-- Inclusion-exclusion turns prescribed singleton blocks into the derangement numbers. -/
theorem card_noFixed (s : Finset ℕ) :
    Fintype.card (NoFixed s) = numDerangements s.card := by
  classical
  let S : (f : ↑s) → Finset (Word s) := fun f =>
    Finset.univ.filter fun p => hat p.1 f.1 = f.1
  have hIE := Finset.inclusion_exclusion_card_inf_compl (Finset.univ : Finset ↑s) S
  have hleft :
      (Finset.univ.inf fun f : ↑s => (S f)ᶜ) =
        Finset.univ.filter (fun p : Word s => ∀ f ∈ s, hat p.1 f ≠ f) := by
    ext p
    simp only [Finset.mem_inf, Finset.mem_univ, true_implies, Finset.mem_compl,
      Finset.mem_filter, true_and, S]
    constructor
    · intro h f hf hfix
      exact h ⟨f, hf⟩ (by simpa using hfix)
    · intro h f hfix
      exact h f.1 f.2 (by simpa using hfix)
  rw [hleft] at hIE
  have hinter : ∀ t : Finset ↑s,
      (t.inf S).card = (s.card - t.card).factorial := by
    intro t
    let F : Finset ℕ := t.image Subtype.val
    have hFs : F ⊆ s := by
      intro f hf
      rcases Finset.mem_image.mp hf with ⟨g, hgt, rfl⟩
      exact g.2
    have hcardF : F.card = t.card := Finset.card_image_of_injective t Subtype.val_injective
    have he : ↑(t.inf S) ≃ ForcedFixed s F :=
      Equiv.subtypeEquivRight fun p => by
        simp only [Finset.mem_inf, S, Finset.mem_filter, Finset.mem_univ, true_and, F]
        constructor
        · intro h f hf
          rcases Finset.mem_image.mp hf with ⟨g, hgt, rfl⟩
          exact h g hgt
        · intro h g hgt
          exact h g.1 (Finset.mem_image.mpr ⟨g, hgt, rfl⟩)
    rw [← Fintype.card_coe, Fintype.card_congr he, card_forcedFixed hFs, hcardF]
  simp_rw [hinter] at hIE
  have hpowerset :
      ∑ t ∈ (Finset.univ : Finset ↑s).powerset,
          (-1 : ℤ) ^ t.card * ((s.card - t.card).factorial : ℤ) =
        ∑ k ∈ Finset.range (s.card + 1),
          (-1 : ℤ) ^ k * Nat.ascFactorial (k + 1) (s.card - k) := by
    rw [Finset.sum_powerset_apply_card
      (fun k => (-1 : ℤ) ^ k * ((s.card - k).factorial : ℤ))]
    simp only [Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hks : k ≤ s.card := by simpa using Finset.mem_range.mp hk
    rw [Nat.ascFactorial_eq_factorial_mul_choose]
    have hsum : k + (s.card - k) = s.card := Nat.add_sub_of_le hks
    rw [hsum, Nat.choose_symm hks]
    norm_num
    ring
  rw [hpowerset, ← numDerangements_sum] at hIE
  rw [Fintype.card_subtype]
  exact_mod_cast hIE

/-- Words whose set of `hat`-fixed entries is exactly `F`. -/
abbrev ExactFixed (s F : Finset ℕ) :=
  {p : Word s // ∀ f ∈ s, hat p.1 f = f ↔ f ∈ F}

/-- A fresh singleton block extends the exact fixed-point set by precisely its new value. -/
def exactInsertEquiv (s F : Finset ℕ) (f : ℕ) (hf : f ∉ s) :
    ExactFixed s F ≃ ExactFixed (insert f s) (insert f F) where
  toFun p := ⟨insertWord s f hf p.1, by
    intro g hg
    rcases Finset.mem_insert.mp hg with hgf | hgS
    · subst g
      simp only [Finset.mem_insert, true_or, iff_true]
      exact (fixedWordEquiv s f hf p.1).2
    · have hpperm : p.1.1.Perm s.toList := by
        simpa [words, List.mem_permutations] using p.1.2
      have hpNodup : p.1.1.Nodup := hpperm.nodup_iff.mpr s.nodup_toList
      have hgf : g ≠ f := by rintro rfl; exact hf hgS
      have hgmem : g ∈ p.1.1 := hpperm.mem_iff.mpr (by simpa using hgS)
      change hat (fixedInsert f p.1.1) g = g ↔ g ∈ insert f F
      rw [hat_fixed_fixedInsert_iff hpNodup (by
        intro hmem
        exact hf (by simpa using hpperm.mem_iff.mp hmem)) hgmem hgf.symm]
      rw [p.2 g hgS]
      simp [hgf]⟩
  invFun p := by
    let pf : {q : Word (insert f s) // hat q.1 f = f} :=
      ⟨p.1, (p.2 f (Finset.mem_insert_self f s)).mpr (Finset.mem_insert_self f F)⟩
    let q : Word s := (fixedWordEquiv s f hf).symm pf
    refine ⟨q, ?_⟩
    intro g hgS
    have hgf : g ≠ f := by rintro rfl; exact hf hgS
    have hqperm : q.1.Perm s.toList := by
      simpa [words, List.mem_permutations] using q.2
    have hqNodup : q.1.Nodup := hqperm.nodup_iff.mpr s.nodup_toList
    have hgmem : g ∈ q.1 := hqperm.mem_iff.mpr (by simpa using hgS)
    have heq := (fixedWordEquiv s f hf).apply_symm_apply pf
    have hlists : fixedInsert f q.1 = p.1.1 := congrArg (fun z => z.1.1) heq
    rw [← hat_fixed_fixedInsert_iff hqNodup (by
      intro hmem
      exact hf (by simpa using hqperm.mem_iff.mp hmem)) hgmem hgf.symm, hlists]
    rw [p.2 g (Finset.mem_insert_of_mem hgS)]
    simp [hgf]
  left_inv p := by
    apply Subtype.ext
    change (fixedWordEquiv s f hf).symm ((fixedWordEquiv s f hf) p.1) = p.1
    exact (fixedWordEquiv s f hf).symm_apply_apply p.1
  right_inv p := by
    apply Subtype.ext
    let pf : {q : Word (insert f s) // hat q.1 f = f} :=
      ⟨p.1, (p.2 f (Finset.mem_insert_self f s)).mpr (Finset.mem_insert_self f F)⟩
    change insertWord s f hf ((fixedWordEquiv s f hf).symm pf) = p.1
    exact congrArg Subtype.val ((fixedWordEquiv s f hf).apply_symm_apply pf)

/-- Prescribing the exact fixed-point set leaves a derangement on the complementary support. -/
theorem card_exactFixed {s F : Finset ℕ} (hFs : F ⊆ s) :
    Fintype.card (ExactFixed s F) = numDerangements (s.card - F.card) := by
  induction F using Finset.induction generalizing s with
  | empty =>
      simpa [ExactFixed, NoFixed] using card_noFixed s
  | @insert f F hfF ih =>
      have hfs : f ∈ s := hFs (Finset.mem_insert_self f F)
      have hFsub : F ⊆ s.erase f := by
        intro g hg
        exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hfF hg,
          hFs (Finset.mem_insert_of_mem hg)⟩
      have he := exactInsertEquiv (s.erase f) F f (by simp)
      have hcard := Fintype.card_congr he
      rw [Finset.insert_erase hfs] at hcard
      rw [← hcard, ih hFsub]
      apply congrArg numDerangements
      rw [Finset.card_erase_of_mem hfs, Finset.card_insert_of_notMem hfF]
      omega

end

end D5.S3.Combinatorics.ArrowWilfCountingCore
