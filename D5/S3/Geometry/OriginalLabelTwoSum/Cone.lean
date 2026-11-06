/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Cone
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Cone
   mirror-E: none(waiver:original-label-two-sum-cone)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Descending native cone schedules and the genuine terminal Gamma branch handle removal of the left core vertex. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Fibre

/-! UNCOMPILED. Cone schedules are actual finite ordinary lists. The terminal
construction takes only the right Gamma and original grounds; it does not take
a parent contraction or a desired endpoint certificate. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every ordinary cone, on the full unchanged original ground, collapses to
its actual apex by the descending list of nonempty faces avoiding that apex. -/
def collapseCone (W : Finset V) (K : Family V) (p : V)
    (hs : Supported W K) (hp : ({p} : Finset V) ∈ K)
    (hcone : ∀ s ∈ K, insert p s ∈ K) :
    Sequence (project K) (project (delta {p})) := by
  classical
  let F := (W.erase p).powerset.filter (fun s => s.Nonempty ∧ s ∈ K)
  have hF (s : Finset V) : s ∈ F ↔ s ⊆ W.erase p ∧ s.Nonempty ∧ s ∈ K := by
    simp [F]
  have hdisj : Disjoint ({p} : Finset V) (W.erase p) := by simp
  have hmem : ∀ t ∈ F, ∅ ∪ t ∈ K ∧ insert p (∅ ∪ t) ∈ K := by
    intro t ht
    have hh := (hF t).mp ht
    simpa using And.intro hh.2.2 (hcone t hh.2.2)
  have hc : ∀ t ∈ F, ∀ s ∈ K, ∅ ∪ t ⊆ s →
      ∃ u ∈ F, t ⊆ u ∧ (s = ∅ ∪ u ∨ s = insert p (∅ ∪ u)) := by
    intro t ht s hK hts
    have hts' : t ⊆ s := by simpa using hts
    have hne := (hF t).mp ht |>.2.1
    have htp : p ∉ t := by
      intro hpt
      exact (Finset.mem_erase.mp ((hF t).mp ht |>.1 <| hpt)).1 rfl
    refine ⟨s.erase p,(hF _).mpr ⟨?_,?_,K.lower (Finset.erase_subset p s) hK⟩,?_,?_⟩
    · intro v hv
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1,
        hs s hK (Finset.mem_erase.mp hv).2⟩
    · obtain ⟨v,hv⟩ := hne
      exact ⟨v,Finset.mem_erase.mpr ⟨fun he => htp (he ▸ hv),hts' hv⟩⟩
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun he => htp (he ▸ hv),hts' hv⟩
    · by_cases hps : p ∈ s
      · right; simpa using (Finset.insert_erase hps).symm
      · left; simp [Finset.erase_eq_of_notMem hps]
  let S := rectangle {p} (W.erase p) ∅ p hdisj (Finset.empty_subset _) (by simp)
    (by simp) F K (fun t ht => ((hF t).mp ht).1)
    (by intro t ht; simpa using ((hF t).mp ht).2.1) hmem hc
  refine S.cast rfl ?_
  congr 1
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hK,hnot⟩
    intro v hv
    by_contra hvp
    have hsingle : {v} ∈ F := (hF _).mpr ⟨by
      simpa using Finset.mem_erase.mpr ⟨(by simpa only [Finset.mem_singleton] using hvp),hs s hK hv⟩,
      by simp,K.lower (Finset.singleton_subset_iff.mpr hv) hK⟩
    apply hnot {v} (Finset.mem_image.mpr ⟨{v},hsingle,by simp only [Finset.empty_union]⟩)
    simpa using Finset.singleton_subset_iff.mpr hv
  · intro hsub
    refine ⟨K.lower hsub hp,?_⟩
    intro a ha has
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
    have ht' : t ⊆ s := by simpa using has
    obtain ⟨v,hv⟩ := ((hF t).mp ht).2.1
    have hvp : v = p := by simpa using hsub (ht' hv)
    exact (Finset.mem_erase.mp (((hF t).mp ht).1 hv)).1 hvp

private theorem join_support (X Y : Finset V) (E : Family V)
    (hE : Supported Y E) : Supported (X ∪ Y) (rawJoin (delta X) E) := by
  rintro s ⟨a,ha,b,hb,rfl⟩
  exact Finset.union_subset_union ha (hE b hb)

/-- Terminal p=e branch with X nonempty: run the supplied right Gamma in the
Y-piece, fixing the whole delta(X)*E term, before using an original X-apex. -/
def terminalGamma (X Y : Finset V) (E : Family V)
    (hXY : Disjoint X Y) (hE : Supported Y E)
    (h0 : (∅ : Finset V) ∈ E)
    (G : Sequence (project (delta Y)) (project E)) :
    Sequence (project (delta Y ⊔ rawJoin (delta X) E))
      (project (rawJoin (delta X) E)) := by
  let B := rawJoin (delta X) E
  have hbase : ∀ t ⊆ Y, ∅ ∪ t ∈ B → t ∈ E := by
    rintro t ht ⟨a,ha,b,hb,he⟩
    apply E.lower ?_ hb
    intro v hvT
    have hab : v ∈ a ∪ b := by rw [← he]; simpa using hvT
    rcases Finset.mem_union.mp hab with hva | hvb
    · exact False.elim (Finset.disjoint_left.mp hXY (ha hva) (ht hvT))
    · exact hvb
  let S := liftFibre (delta Y) E B ∅ Y (by change (∅ : Finset V) ⊆ Y; exact Finset.empty_subset _) h0 G (by simp)
    (fun _ hs => hs) (by intro x hx; exact False.elim (Finset.not_ssubset_empty x hx)) hbase
  refine S.cast ?_ ?_
  · congr 1
    rw [(rawJoin_unit (delta Y)).1]
    exact sup_comm _ _
  · congr 1
    rw [(rawJoin_unit E).1]
    apply sup_eq_left.mpr
    intro s hs
    exact ⟨∅,by simp,s,hs,by simp⟩

/-- Output type records the computed original vertex, not an assumed endpoint. -/
def terminalAtInterface (X Y R : Finset V) (E : Family V)
    (hXY : Disjoint X Y) (hR : R ⊆ Y) (hRne : R.Nonempty)
    (hE : Supported Y E) (h0 : (∅ : Finset V) ∈ E)
    (G : Sequence (project (delta Y)) (project E)) :
    Σ p : {p : V // p ∈ X ∪ Y},
      Sequence (project (delta Y ⊔ rawJoin (delta X) E))
        (project (delta {p.1})) := by
  classical
  by_cases hX : X.Nonempty
  · let p := hX.choose
    have hp : p ∈ X := hX.choose_spec
    have hpB : ({p} : Finset V) ∈ rawJoin (delta X) E :=
      ⟨{p},Finset.singleton_subset_iff.mpr hp,∅,h0,by simp⟩
    have hcone : ∀ s ∈ rawJoin (delta X) E,
        insert p s ∈ rawJoin (delta X) E := by
      rintro s ⟨a,ha,b,hb,rfl⟩
      exact ⟨insert p a,Finset.insert_subset_iff.mpr ⟨hp,ha⟩,b,hb,by simp⟩
    exact ⟨⟨p,Finset.mem_union_left _ hp⟩,
      (terminalGamma X Y E hXY hE h0 G).append
        (collapseCone (X ∪ Y) (rawJoin (delta X) E) p
          (join_support X Y E hE) hpB hcone)⟩
  · have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    let p := hRne.choose
    have hp : p ∈ Y := hR hRne.choose_spec
    have hsource : delta Y ⊔ rawJoin (delta X) E = delta Y := by
      rw [hXe,(rawJoin_unit E).1]
      exact sup_eq_left.mpr hE
    exact ⟨⟨p,Finset.mem_union_right _ hp⟩,
      (collapseCone Y (delta Y) p (fun _ hs => hs)
        (Finset.singleton_subset_iff.mpr hp)
        (fun s hs => Finset.insert_subset_iff.mpr ⟨hp,hs⟩)).cast
          (congrArg project hsource).symm rfl⟩

end D5.S3.Geometry.OriginalLabelTwoSum
