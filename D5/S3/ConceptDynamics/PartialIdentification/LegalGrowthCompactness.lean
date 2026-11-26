/- GID: D5/S3/ConceptDynamics/PartialIdentification/LegalGrowthCompactness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/LegalGrowthCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal growth compactness is equivalent to finite enabled frontiers. -/

module

public import D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
public import Mathlib.Topology.Compactness.Compact

/-! Compactness for injective locally legal growth in an arbitrary discrete partial order. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.LegalGrowthCompactness

open EnabledPathSwapConnectivity

universe u

variable {E : Type u} [PartialOrder E]

/-- Infinite growth adds a fresh event only after all its strict predecessors. -/
def Omega (E : Type u) [PartialOrder E] : Set (ℕ → E) :=
  {f | Function.Injective f ∧
    ∀ (i : ℕ) (x : E), x < f i → ∃ j : ℕ, j < i ∧ f j = x}

private noncomputable def stem (f : ℕ → E) (n : ℕ) : Finset E :=
  by classical exact (Finset.range n).image f

omit [PartialOrder E] in
private theorem mem_stem (f : ℕ → E) (n : ℕ) (x : E) :
    x ∈ stem f n ↔ ∃ j < n, f j = x := by
  classical
  simp [stem]

private theorem stem_lower {f : ℕ → E} (hf : f ∈ Omega E) (n : ℕ) :
    IsLowerSet (stem f n : Set E) := by
  intro y x hxy hy
  obtain ⟨i, hi, rfl⟩ := (mem_stem f n y).mp hy
  by_cases he : x = f i
  · exact he ▸ (mem_stem f n (f i)).mpr ⟨i, hi, rfl⟩
  · obtain ⟨j, hj, heq⟩ := hf.2 i x (lt_of_le_of_ne hxy he)
    exact (mem_stem f n x).mpr ⟨j, hj.trans hi, heq⟩

private theorem next_enabled {f : ℕ → E} (hf : f ∈ Omega E) (n : ℕ) :
    Enabled (stem f n : Set E) (f n) := by
  constructor
  · intro hn
    obtain ⟨j, hj, he⟩ := (mem_stem f n (f n)).mp hn
    exact hj.ne (hf.1 he)
  · intro y hy
    exact (mem_stem f n y).mpr (hf.2 n y hy)

private theorem finite_stems
    (h : ∀ F : Finset E, IsLowerSet (F : Set E) → {x | Enabled (F : Set E) x}.Finite) :
    ∀ n : ℕ, {F : Finset E | ∃ f ∈ Omega E, stem f n = F}.Finite := by
  classical
  intro n
  induction n with
  | zero =>
      apply (Set.finite_singleton (∅ : Finset E)).subset
      rintro F ⟨f, hf, rfl⟩
      simp [stem]
  | succ n ih =>
      have hbound := ih.biUnion fun F hF =>
        (h F (by obtain ⟨f, hf, rfl⟩ := hF; exact stem_lower hf n)).image
          (fun x => insert x F)
      apply hbound.subset
      rintro F ⟨f, hf, rfl⟩
      refine Set.mem_iUnion₂.mpr ⟨stem f n, ⟨f, hf, rfl⟩, ?_⟩
      refine ⟨f n, next_enabled hf n, ?_⟩
      simp [stem, Finset.range_add_one, Finset.image_insert]

private theorem finite_coordinates
    (h : ∀ F : Finset E, IsLowerSet (F : Set E) → {x | Enabled (F : Set E) x}.Finite)
    (n : ℕ) : ((fun f : ℕ → E => f n) '' Omega E).Finite := by
  have hb := (finite_stems h n).biUnion fun F hF =>
    h F (by obtain ⟨f, hf, rfl⟩ := hF; exact stem_lower hf n)
  apply hb.subset
  rintro x ⟨f, hf, rfl⟩
  exact Set.mem_iUnion₂.mpr ⟨stem f n, ⟨f, hf, rfl⟩, next_enabled hf n⟩

private theorem closed_omega [TopologicalSpace E] [DiscreteTopology E] :
    IsClosed (Omega E) := by
  classical
  have hne (i j : ℕ) : IsClosed {f : ℕ → E | f i ≠ f j} := by
    exact IsClosed.preimage (f := fun f : ℕ → E => (f i, f j))
      ((continuous_apply i).prodMk (continuous_apply j))
      (isClosed_discrete {p : E × E | p.1 ≠ p.2})
  have hp (i : ℕ) (x : E) :
      IsClosed {f : ℕ → E | x < f i → ∃ j < i, f j = x} := by
    have ha : IsClosed {f : ℕ → E | ¬ x < f i} :=
      IsClosed.preimage (f := fun f : ℕ → E => f i)
        (continuous_apply i) (isClosed_discrete {y : E | ¬ x < y})
    have hb : IsClosed {f : ℕ → E | ∃ j : Fin i, f j = x} := by
      simpa only [Set.ofPred_exists, Set.preimage, Set.mem_singleton_iff] using
        isClosed_iUnion_of_finite (fun j : Fin i =>
          IsClosed.preimage (f := fun f : ℕ → E => f j.val)
            (continuous_apply j.val) (isClosed_discrete ({x} : Set E)))
    convert ha.union hb using 1
    ext f
    simp only [Set.mem_union, Set.mem_ofPred_eq, imp_iff_not_or]
    exact or_congr Iff.rfl ⟨fun ⟨j, hj, he⟩ => ⟨⟨j, hj⟩, he⟩,
      fun ⟨j, he⟩ => ⟨j.val, j.isLt, he⟩⟩
  have hi : IsClosed {f : ℕ → E | Function.Injective f} := by
    have hc := isClosed_iInter fun i : ℕ => isClosed_iInter fun j : ℕ =>
      isClosed_iInter fun _h : i ≠ j => hne i j
    convert hc using 1
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · exact fun hf i j hij he => hij (hf he)
    · intro hf i j he
      by_contra hij
      exact hf i j hij he
  have hl : IsClosed {f : ℕ → E | ∀ i x, x < f i → ∃ j < i, f j = x} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter (fun i : ℕ => isClosed_iInter (hp i))
  exact hi.inter hl

private theorem append_frontier (F : Finset E) (hF : IsLowerSet (F : Set E))
    (l : List {x : E // x ∈ F})
    (hl : ExtensionList (∅ : Set {x : E // x ∈ F}) Set.univ l)
    (b : ℕ ↪ {x : E // Enabled (F : Set E) x}) :
    ∃ f ∈ Omega E, f l.length = (b 0).val := by
  classical
  let f : ℕ → E := fun n => if h : n < l.length then (l[n]).val else (b (n - l.length)).val
  have hmem (i : ℕ) (hi : i < l.length) : (l[i]).val ∈ F := (l[i]).property
  have hfind (x : E) (hx : x ∈ F) : ∃ j, ∃ hj : j < l.length, (l[j]).val = x := by
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp
      ((hl.2.1 ⟨x, hx⟩).mpr ⟨Set.mem_univ _, Set.notMem_empty _⟩)
    exact ⟨j, hj, congrArg Subtype.val he⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro i j he
    by_cases hi : i < l.length <;> by_cases hj : j < l.length
    · simp only [f, dite_eq_left hi, dite_eq_left hj] at he
      exact hl.1.getElem_inj_iff.mp (Subtype.ext he)
    · simp only [f, dite_eq_left hi, dite_eq_right hj] at he
      exact ((b (j - l.length)).property.1 (he ▸ hmem i hi)).elim
    · simp only [f, dite_eq_right hi, dite_eq_left hj] at he
      exact ((b (i - l.length)).property.1 (he.symm ▸ hmem j hj)).elim
    · simp only [f, dite_eq_right hi, dite_eq_right hj] at he
      have hsub := b.injective (Subtype.ext he)
      omega
  · intro i x hx
    by_cases hi : i < l.length
    · simp only [f, dite_eq_left hi] at hx
      obtain ⟨j, hj, he⟩ := hfind x (hF hx.le (hmem i hi))
      have hji : j < i := by
        by_contra hnot
        have hle : i ≤ j := Nat.le_of_not_gt hnot
        rcases eq_or_lt_of_le hle with hij | hij
        · subst j
          exact hx.ne he.symm
        · exact (List.pairwise_iff_getElem.mp hl.2.2 i j hi hj hij)
            (show l[j] ≤ l[i] from he.symm ▸ hx.le)
      exact ⟨j, hji, by simp only [f, dite_eq_left hj]; exact he⟩
    · simp only [f, dite_eq_right hi] at hx
      obtain ⟨j, hj, he⟩ := hfind x ((b (i - l.length)).property.2 x hx)
      exact ⟨j, by omega, by simp only [f, dite_eq_left hj]; exact he⟩
  · simp [f]

/-- Compactness of the full, possibly nonexhaustive legal-growth space is
equivalent to finite enabled frontiers at every finite lower stem. -/
theorem result [TopologicalSpace E] [DiscreteTopology E] :
    IsCompact (Omega E) ↔
      ∀ F : Finset E, IsLowerSet (F : Set E) →
        {x : E | x ∉ F ∧ ∀ y : E, y < x → y ∈ F}.Finite := by
  classical
  constructor
  · intro hc F hF
    change {x : E | Enabled (F : Set E) x}.Finite
    by_contra hinf
    have hA : {x : E | Enabled (F : Set E) x}.Infinite := hinf
    let a := hA.natEmbedding
    obtain ⟨t, ht⟩ :=
      (EnabledPathSwapConnectivity.result (E := {x : E // x ∈ F})
        ∅ Set.univ (by simp [IsLowerSet]) (by simp [IsLowerSet]) (by simp)).2.1
    have hext :=
      (EnabledPathSwapConnectivity.result (E := {x : E // x ∈ F})
        ∅ Set.univ (by simp [IsLowerSet]) (by simp [IsLowerSet]) (by simp)).1 t |>.mp ht
    have hcoord : ((fun f : ℕ → E => f t.length) '' Omega E).Finite :=
      isCompact_iff_finite.mp (hc.image (continuous_apply t.length))
    apply hA.not_finite
    apply hcoord.subset
    intro x hx
    let b : ℕ ↪ {x : E // Enabled (F : Set E) x} :=
      a.trans (Equiv.swap ⟨x, hx⟩ (a 0)).toEmbedding
    obtain ⟨f, hf, he⟩ := append_frontier F hF t hext b
    refine ⟨f, hf, ?_⟩
    simpa [b] using he
  · intro h
    apply (Pi.isCompact_iff_of_isClosed closed_omega).mpr
    intro n
    exact isCompact_iff_finite.mpr (finite_coordinates h n)

end D5.S3.ConceptDynamics.PartialIdentification.LegalGrowthCompactness
