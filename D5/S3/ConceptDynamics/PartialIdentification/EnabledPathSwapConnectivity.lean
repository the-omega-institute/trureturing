/- GID: D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-poset enabled paths are linear extensions connected by legal adjacent swaps. -/

import Mathlib.Data.Finset.Sort
import Mathlib.Order.Extension.Linear
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity

universe u

variable {E : Type u} [PartialOrder E]

/-- An event is fresh and all its strict predecessors have already occurred. -/
def Enabled (K : Set E) (e : E) : Prop :=
  e ∉ K ∧ ∀ d, d < e → d ∈ K

/-- A list executes by adding one fresh enabled event at each step. -/
def Exec (K : Set E) : List E → Set E → Prop
  | [], J => K = J
  | e :: t, J => Enabled K e ∧ Exec (insert e K) t J

/-- A repetition-free enumeration of the gap, with no predecessor appearing
after its successor. The relation here is the original partial order. -/
def ExtensionList (I J : Set E) (l : List E) : Prop :=
  l.Nodup ∧ (∀ e, e ∈ l ↔ e ∈ J ∧ e ∉ I) ∧
    l.Pairwise (fun a b => ¬ b ≤ a)

/-- A literal adjacent exchange with a shared suffix, legal endpoints, and
two incomparable events enabled at the actual lower-set prefix reached. -/
def LegalSwap (I J : Set E) (l m : List E) : Prop :=
  Exec I l J ∧ Exec I m J ∧
    ∃ (p s : List E) (a b : E) (K : Set E),
      l = p ++ a :: b :: s ∧ m = p ++ b :: a :: s ∧
      Exec I p K ∧ IsLowerSet K ∧ Enabled K a ∧ Enabled K b ∧
      ¬ a ≤ b ∧ ¬ b ≤ a

/-- Every interval of lower sets in a finite poset has an enabled execution.
Its executions are precisely the linear-extension lists of the induced gap,
and any two are connected through actual legal adjacent-swap squares. -/
theorem result [Finite E] (I J : Set E)
    (hI : IsLowerSet I) (hJ : IsLowerSet J) (hIJ : I ⊆ J) :
    (∀ l, Exec I l J ↔ ExtensionList I J l) ∧
    (∃ l, Exec I l J) ∧
    (∀ l m, Exec I l J → Exec I m J →
      Relation.ReflTransGen (LegalSwap I J) l m) := by
  classical
  have lower_insert : ∀ (K : Set E) (a : E),
      IsLowerSet K → Enabled K a → IsLowerSet (insert a K) := by
    intro K a hK ha y x hxy hy
    rcases hy with hya | hy
    · subst y
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr (ha.2 x (lt_of_le_of_ne hxy hxa))
    · exact Or.inr (hK hxy hy)
  have execution_data : ∀ (l : List E) (K L : Set E),
      Exec K l L → K ⊆ L ∧ ExtensionList K L l := by
    intro l
    induction l with
    | nil =>
        intro K L h
        cases h
        exact ⟨Set.Subset.rfl, by simp [ExtensionList]⟩
    | cons a t ih =>
        intro K L h
        rcases h with ⟨ha, ht⟩
        rcases ih (insert a K) L ht with ⟨hsub, hnd, hmem, hpw⟩
        have haL : a ∈ L := hsub (Set.mem_insert a K)
        have hat : a ∉ t := by
          intro ham
          exact (hmem a).1 ham |>.2 (Set.mem_insert a K)
        refine ⟨fun x hx => hsub (Or.inr hx), ?_, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨hat, hnd⟩
        · intro x
          simp only [List.mem_cons]
          constructor
          · rintro (rfl | hx)
            · exact ⟨haL, ha.1⟩
            · exact ⟨((hmem x).1 hx).1,
                fun hxK => ((hmem x).1 hx).2 (Or.inr hxK)⟩
          · rintro ⟨hxL, hxK⟩
            by_cases hxa : x = a
            · exact Or.inl hxa
            · exact Or.inr ((hmem x).2 ⟨hxL, by simpa using And.intro hxa hxK⟩)
        · apply List.pairwise_cons.mpr
          refine ⟨?_, hpw⟩
          intro b hb hba
          have hbK := ((hmem b).1 hb).2
          have hne : b ≠ a := fun h => hbK (Or.inl h)
          exact hbK (Or.inr (ha.2 b (lt_of_le_of_ne hba hne)))
  have extension_exec : ∀ (l : List E) (K L : Set E),
      IsLowerSet K → IsLowerSet L → K ⊆ L →
      ExtensionList K L l → Exec K l L := by
    intro l
    induction l with
    | nil =>
        intro K L _ _ hsub h
        apply Set.Subset.antisymm hsub
        intro x hx
        by_contra hxK
        exact List.not_mem_nil ((h.2.1 x).2 ⟨hx, hxK⟩)
    | cons a t ih =>
        intro K L hK hL hsub h
        rcases h with ⟨hnd, hmem, hpw⟩
        rcases List.nodup_cons.mp hnd with ⟨hat, hnd⟩
        rcases List.pairwise_cons.mp hpw with ⟨hhead, hpw⟩
        have ha := (hmem a).1 (List.mem_cons_self ..)
        have hen : Enabled K a := by
          refine ⟨ha.2, ?_⟩
          intro d hda
          by_contra hdK
          have hdl := (hmem d).2 ⟨hL hda.le ha.1, hdK⟩
          rcases List.mem_cons.mp hdl with h | h
          · exact hda.ne h
          · exact hhead d h hda.le
        refine ⟨hen, ih (insert a K) L (lower_insert K a hK hen) hL ?_ ?_⟩
        · exact Set.insert_subset ha.1 hsub
        · refine ⟨hnd, ?_, hpw⟩
          intro x
          constructor
          · intro hx
            have hxL := (hmem x).1 (List.mem_cons_of_mem a hx)
            refine ⟨hxL.1, ?_⟩
            rintro (rfl | hxK)
            · exact hat hx
            · exact hxL.2 hxK
          · rintro ⟨hxL, hxK⟩
            have hx := (hmem x).2 ⟨hxL, fun h => hxK (Or.inr h)⟩
            rcases List.mem_cons.mp hx with h | h
            · exact (hxK (Or.inl h)).elim
            · exact h
  have correspondence : ∀ l, Exec I l J ↔ ExtensionList I J l :=
    fun l => ⟨fun h => (execution_data l I J h).2,
      extension_exec l I J hI hJ hIJ⟩
  have existence : ∃ l, Exec I l J := by
    let : Fintype E := Fintype.ofFinite E
    obtain ⟨r, hr, hext⟩ := extend_partialOrder ((· ≤ ·) : E → E → Prop)
    let : IsLinearOrder E r := hr
    let gap : Finset E := Finset.univ.filter (fun e => e ∈ J ∧ e ∉ I)
    refine ⟨gap.sort r, (correspondence _).2 ?_⟩
    refine ⟨gap.sort_nodup r, ?_, ?_⟩
    · intro e
      simp [gap, Finset.mem_sort]
    · have hboth := (gap.pairwise_sort r).and (gap.sort_nodup r)
      exact hboth.imp fun {a b} hab hba => hab.2 (antisymm hab.1 (hext _ _ hba))
  have lift_swap : ∀ (K L : Set E) (a : E), Enabled K a →
      ∀ l m, LegalSwap (insert a K) L l m →
        LegalSwap K L (a :: l) (a :: m) := by
    intro K L a ha l m h
    rcases h with ⟨hl, hm, p, s, b, c, P, heql, heqm, hp, hP, hb, hc, hbc, hcb⟩
    refine ⟨⟨ha, hl⟩, ⟨ha, hm⟩, a :: p, s, b, c, P, ?_, ?_, ?_,
      hP, hb, hc, hbc, hcb⟩
    · simp [heql]
    · simp [heqm]
    · exact ⟨ha, hp⟩
  have bubble : ∀ (p : List E) (K L : Set E) (a : E) (q : List E),
      IsLowerSet K → Enabled K a → Exec K (p ++ a :: q) L →
      Relation.ReflTransGen (LegalSwap K L) (p ++ a :: q) (a :: (p ++ q)) ∧
        Exec K (a :: (p ++ q)) L := by
    intro p
    induction p with
    | nil =>
        intro K L a q _ _ h
        exact ⟨Relation.ReflTransGen.refl, h⟩
    | cons b p ih =>
        intro K L a q hK ha h
        rcases h with ⟨hb, ht⟩
        have ha_tail : a ∈ p ++ a :: q := by simp
        have hafresh : a ∉ insert b K :=
          ((execution_data _ _ _ ht).2.2.1 a).1 ha_tail |>.2
        have hab : a ≠ b := fun heq => hafresh (Or.inl heq)
        have ha_after_b : Enabled (insert b K) a :=
          ⟨hafresh, fun d hd => Or.inr (ha.2 d hd)⟩
        obtain ⟨htchain, htend⟩ :=
          ih (insert b K) L a q (lower_insert K b hK hb) ha_after_b ht
        have hba : ¬ b ≤ a := by
          intro hle
          exact hb.1 (ha.2 b (lt_of_le_of_ne hle hab.symm))
        have hab' : ¬ a ≤ b := by
          intro hle
          exact ha.1 (hb.2 a (lt_of_le_of_ne hle hab))
        have hb_after_a : Enabled (insert a K) b :=
          ⟨by simp [hab.symm, hb.1], fun d hd => Or.inr (hb.2 d hd)⟩
        have square_cut : insert a (insert b K) = insert b (insert a K) :=
          Set.insert_comm a b K
        have hsuffix : Exec (insert b (insert a K)) (p ++ q) L := by
          rw [← square_cut]
          exact htend.2
        have hend : Exec K (a :: b :: (p ++ q)) L :=
          ⟨ha, hb_after_a, hsuffix⟩
        have hswap : LegalSwap K L (b :: a :: (p ++ q)) (a :: b :: (p ++ q)) := by
          refine ⟨⟨hb, htend⟩, hend, [], p ++ q, b, a, K,
            rfl, rfl, rfl, hK, hb, ha, hba, hab'⟩
        have hfront := Relation.ReflTransGen.lift (List.cons b)
          (lift_swap K L b hb) _ _ htchain
        exact ⟨hfront.trans (Relation.ReflTransGen.single hswap), hend⟩
  have connected : ∀ (m : List E) (K : Set E),
      IsLowerSet K → K ⊆ J → ∀ l, Exec K l J → Exec K m J →
      Relation.ReflTransGen (LegalSwap K J) l m := by
    intro m
    induction m with
    | nil =>
        intro K _ _ l hl hm
        change K = J at hm
        subst K
        cases l with
        | nil => exact Relation.ReflTransGen.refl
        | cons a t =>
            have ha := ((execution_data _ _ _ hl).2.2.1 a).1 (List.mem_cons_self ..)
            exact (ha.2 ha.1).elim
    | cons a t ih =>
        intro K hK hKJ l hl hm
        have ha : Enabled K a := hm.1
        have haJ := ((execution_data _ _ _ hm).2.2.1 a).1 (List.mem_cons_self ..)
        have hal : a ∈ l := ((execution_data _ _ _ hl).2.2.1 a).2 haJ
        obtain ⟨p, q, rfl⟩ := List.mem_iff_append.mp hal
        obtain ⟨hchain, hend⟩ := bubble p K J a q hK ha hl
        have htail := ih (insert a K) (lower_insert K a hK ha)
          (Set.insert_subset haJ.1 hKJ) (p ++ q) hend.2 hm.2
        exact hchain.trans (Relation.ReflTransGen.lift (List.cons a)
          (lift_swap K J a ha) _ _ htail)
  exact ⟨correspondence, existence, fun l m => connected m I hI hIJ l⟩

#print axioms result

end D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
