/- GID: D5/S3/Arith/Additive/BenfieldLippard/Stabilization
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/BenfieldLippard/Stabilization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive missing offsets stabilize at the gaps of the shifted-power monoid. -/

import D5.S3.Arith.Additive.BenfieldLippard.PositiveFixedLength
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace BenfieldLippard

def exceptions (k j : ℕ) : Set ℕ :=
  {s | 0 < s ∧ ¬ PosRep k j (j + s)}

def generators (k : ℕ) : Set ℕ :=
  (fun a : ℕ ↦ a ^ k - 1) '' {a | 0 < a}

def offsets (k : ℕ) : AddSubmonoid ℕ := AddSubmonoid.closure (generators k)

def gaps (k : ℕ) : Set ℕ := {s | 0 < s ∧ s ∉ offsets k}

theorem generator_mem (k : ℕ) {a : ℕ} (ha : 0 < a) : a ^ k - 1 ∈ offsets k :=
  AddSubmonoid.subset_closure ⟨a, ha, rfl⟩

private theorem posRep_add {k j l s t : ℕ}
    (hs : PosRep k j (j + s)) (ht : PosRep k l (l + t)) :
    PosRep k (j + l) (j + l + (s + t)) := by
  obtain ⟨f, hf, hsf⟩ := hs
  obtain ⟨g, hg, htg⟩ := ht
  refine ⟨Fin.addCases f g, ?_, ?_⟩
  · intro i
    refine Fin.addCases (motive := fun i ↦ 0 < Fin.addCases f g i) ?_ ?_ i
    · intro a
      simpa using hf a
    · intro b
      simpa using hg b
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    omega

private theorem posRep_pad {k i j s : ℕ} (hij : i ≤ j)
    (h : PosRep k i (i + s)) : PosRep k j (j + s) := by
  have h1 : PosRep k (j - i) ((j - i) + 0) := by
    exact ⟨fun _ ↦ 1, fun _ ↦ Nat.one_pos, by simp⟩
  simpa [Nat.add_sub_of_le hij] using posRep_add h h1

theorem offset_iff_exists_posRep {k s : ℕ} : s ∈ offsets k ↔ ∃ j, PosRep k j (j + s) := by
  constructor
  · intro h
    change s ∈ AddSubmonoid.closure (generators k) at h
    induction h using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨1, fun _ ↦ a, fun _ ↦ ha, ?_⟩
      have ha' : 0 < a ^ k := pow_pos ha _
      simp only [Fin.sum_univ_one]
      omega
    | zero => exact ⟨0, Fin.elim0, (fun i ↦ Fin.elim0 i), by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨j, hj⟩ := hx
      obtain ⟨l, hl⟩ := hy
      exact ⟨j + l, posRep_add hj hl⟩
  · rintro ⟨j, f, hf, he⟩
    have sum_mem : (∑ i : Fin j, (f i ^ k - 1)) ∈ offsets k :=
      sum_mem fun i _ ↦ generator_mem k (hf i)
    have eq : j + s = (∑ i : Fin j, (f i ^ k - 1)) + j := by
      calc
        _ = ∑ i : Fin j, f i ^ k := he
        _ = ∑ i : Fin j, (f i ^ k - 1 + 1) :=
          Finset.sum_congr rfl fun i _ ↦ (Nat.sub_add_cancel (pow_pos (hf i) k)).symm
        _ = _ := by simp [Finset.sum_add_distrib]
    have : s = ∑ i : Fin j, (f i ^ k - 1) := by omega
    rwa [this]

theorem stabilization (k : ℕ) (hk : 2 ≤ k) :
    (gaps k).Finite ∧ ∃ J ≥ 1, ∀ j ≥ J, exceptions k j = gaps k := by
  classical
  obtain ⟨j₀, hj₀, N, hN⟩ := BenfieldLippard.eventual_fixed_length k hk
  have hfinite : (exceptions k j₀).Finite := by
    refine (Finset.range N).finite_toSet.subset ?_
    intro s hs
    apply Finset.mem_range.mpr
    exact lt_of_not_ge fun h ↦ hs.2 (hN (j₀ + s) (by omega))
  have gaps_subset (j : ℕ) : gaps k ⊆ exceptions k j :=
    fun _ hs ↦ ⟨hs.1, fun hr ↦ hs.2 (offset_iff_exists_posRep.mpr ⟨j, hr⟩)⟩
  let candidates : Finset ℕ := hfinite.toFinset.filter (· ∈ offsets k)
  have candidate_mem : ∀ s ∈ candidates, ∃ l, PosRep k l (l + s) :=
    fun s hs ↦ offset_iff_exists_posRep.mp (Finset.mem_filter.mp hs).2
  choose len hlen using candidate_mem
  let lengths : Finset ℕ := candidates.attach.image (fun (s : {s // s ∈ candidates}) ↦ len s.val s.property)
  let J := max j₀ (lengths.sup id)
  refine ⟨hfinite.subset (gaps_subset j₀), J, ?_, fun j hj ↦ ?_⟩
  · exact hj₀.trans (le_max_left _ _)
  · apply Set.Subset.antisymm ?_ (gaps_subset j)
    intro s hs
    refine ⟨hs.1, fun hm ↦ hs.2 ?_⟩
    by_cases hs₀ : s ∈ exceptions k j₀
    · have hc : s ∈ candidates :=
        Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr hs₀, hm⟩
      have hl : len s hc ∈ lengths :=
        Finset.mem_image.mpr ⟨⟨s, hc⟩, Finset.mem_attach _ _, rfl⟩
      exact posRep_pad ((Finset.le_sup (f := id) hl).trans ((le_max_right _ _).trans hj))
        (hlen s hc)
    · have hr : PosRep k j₀ (j₀ + s) := by
        by_contra hn
        exact hs₀ ⟨hs.1, hn⟩
      exact posRep_pad ((le_max_left _ _).trans hj) hr

end BenfieldLippard
