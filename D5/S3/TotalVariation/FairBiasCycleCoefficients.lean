/- GID: D5/S3/TotalVariation/FairBiasCycleCoefficients
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasCycleCoefficients
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Unit coefficients in normalized signed fair-bias cycles. -/

import D5.S3.TotalVariation.FairBiasChainContraction
import Mathlib.Combinatorics.Matroid.Circuit

/-! The least internally active element gives a ridge whose elimination
has at most one contribution to each normalized top cycle. -/

set_option autoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.TotalVariation.FairBiasCycleCoefficients

section Exchange

variable {V : Type*} [LinearOrder V] {M : Matroid V}

/-- A member of a basis is passive if it can be exchanged for a smaller element. -/
private def Passive (M : Matroid V) (S : Set V) (a : V) : Prop :=
  ∃ x ∉ S, x < a ∧ M.IsBase (insert x (S \ {a}))

omit [LinearOrder V] in
private theorem indep_after_obstructed_exchange
    {R : Set V} {a b x y : V}
    (hx : M.Indep (insert x (insert b R)))
    (hy : M.Indep (insert y (insert a R)))
    (hxR : x ∉ insert b R) (hyR : y ∉ insert a R)
    (hn : ¬ M.Indep (insert x (insert a R))) :
    M.Indep (insert x (insert y R)) := by
  have hRa := hy.subset (Set.subset_insert _ _)
  have hRb := hx.subset (Set.subset_insert _ _)
  have hxG := hx.subset_ground (Set.mem_insert _ _)
  have hyG := hy.subset_ground (Set.mem_insert _ _)
  have hxNot : x ∉ M.closure R := fun hxcl =>
    ((hRb.insert_indep_iff_of_notMem hxR).mp hx).2
      (M.closure_subset_closure (Set.subset_insert _ _) hxcl)
  have hxIn : x ∈ M.closure (insert a R) := by
    by_contra h
    exact hn (hRa.insert_indep_iff.mpr (.inl ⟨hxG, h⟩))
  have hcl := Matroid.closure_insert_congr (M := M) ⟨hxIn, hxNot⟩
  rw [Set.insert_comm]
  apply (hx.subset (by intro u hu; aesop) : M.Indep (insert x R)).insert_indep_iff.mpr
  exact .inl ⟨hyG, fun h => ((hRa.insert_indep_iff_of_notMem hyR).mp hy).2 (hcl ▸ h)⟩

private theorem passive_persists
    {S : Set V} {a b x : V}
    (hS : M.IsBase S) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hxa : a < x) (hx : x ∉ S) (hactive : ¬ Passive M S a)
    (hT : M.IsBase (insert x (S \ {a}))) (hpassive : Passive M S b) :
    Passive M (insert x (S \ {a})) b := by
  obtain ⟨y, hy, hyb, hY⟩ := hpassive
  let R := (S \ {a}) \ {b}
  have hRa : insert a R = S \ {b} := by
    ext u
    simp only [R, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    by_cases hua : u = a
    · subst u
      simp [ha, hab]
    · simp [hua]
  have hRb : insert b R = S \ {a} := by
    ext u
    simp only [R, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    by_cases hub : u = b
    · subst u
      simp [hb, hab.symm]
    · tauto
  have hrem : insert x (S \ {a}) \ {b} = insert x R := by
    have hxb : x ≠ b := fun h => hx (h ▸ hb)
    rw [Set.insert_sdiff_singleton_comm hxb]
  have hxRb : x ∉ insert b R := by rw [hRb]; exact fun h => hx h.1
  have hyRa : y ∉ insert a R := by rw [hRa]; exact fun h => hy h.1
  have hxB : M.Indep (insert x (insert b R)) := hRb ▸ hT.indep
  have hyB : M.Indep (insert y (insert a R)) := hRa ▸ hY.indep
  by_cases hax : a < b ∧ M.Indep (insert x (S \ {b}))
  · refine ⟨a, ?_, hax.1, ?_⟩
    · have hne : a ≠ x := ne_of_lt hxa
      simp [hne]
    · rw [hrem, Set.insert_comm, hRa]
      exact hS.exchange_isBase_of_indep hx hax.2
  have hyx : y ≠ x := by
    intro eq
    subst y
    exact hax ⟨hxa.trans hyb, hY.indep⟩
  have hyT : y ∉ insert x (S \ {a}) := by
    simp [hyx, hy]
  refine ⟨y, hyT, hyb, hT.exchange_isBase_of_indep hyT ?_⟩
  rw [hrem]
  by_cases hab' : a < b
  · rw [Set.insert_comm]
    apply indep_after_obstructed_exchange hxB hyB hxRb hyRa
    rw [hRa]
    exact fun hxind => hax ⟨hab', hxind⟩
  · have hya : y < a := hyb.trans (lt_of_le_of_ne (le_of_not_gt hab') hab.symm)
    apply indep_after_obstructed_exchange hyB hxB hyRa hxRb
    rw [hRb]
    exact fun hyind => hactive ⟨y, hy, hya, hS.exchange_isBase_of_indep hy hyind⟩

omit [LinearOrder V] in
private theorem unique_admissible_insert
    {F B : Set V} {a x y : V}
    (hF : M.IsBase F) (hB : M.Indep B) (ha : a ∈ F) (haB : a ∉ B)
    (hxF : x ∉ F) (hyF : y ∉ F) (hxB : x ∈ B) (hyB : y ∈ B)
    (hxG : x ∈ M.E) (hyG : y ∈ M.E)
    (hxa : M.IsBase (insert x (F \ {a})))
    (hxonly : ∀ b ∈ F, b ∉ B → b ≠ a → ¬ M.IsBase (insert x (F \ {b})))
    (hyonly : ∀ b ∈ F, b ∉ B → b ≠ a → ¬ M.IsBase (insert y (F \ {b}))) :
    x = y := by
  let R := F ∩ B
  have closed (v : V) (hvF : v ∉ F) (hvG : v ∈ M.E)
      (honly : ∀ b ∈ F, b ∉ B → b ≠ a → ¬ M.IsBase (insert v (F \ {b}))) :
      v ∈ M.closure (insert a R) := by
    have hva : v ≠ a := Ne.symm (ne_of_mem_of_not_mem ha hvF)
    rw [Matroid.mem_closure_iff_exists_isCircuit (by simp [R, hvF, hva])]
    refine ⟨M.fundCircuit v F, ?_, hF.fundCircuit_isCircuit hvG hvF, M.mem_fundCircuit v F⟩
    intro b hb
    rcases M.fundCircuit_subset_insert v F hb with he | hbF
    · exact .inl he
    by_cases hba : b = a
    · exact .inr (.inl hba)
    have hbB : b ∈ B := by
      by_contra hn
      have hbI := (hF.indep.mem_fundCircuit_iff (by rwa [hF.closure_eq]) hvF).mp hb
      rw [← Set.insert_sdiff_singleton_comm (Ne.symm (ne_of_mem_of_not_mem hbF hvF))] at hbI
      exact honly b hbF hn hba (hF.exchange_isBase_of_indep hvF hbI)
    exact .inr (.inr ⟨hbF, hbB⟩)
  have hxcl := closed x hxF hxG hxonly
  have hycl := closed y hyF hyG hyonly
  have hxNot : x ∉ M.closure R := by
    intro h
    have hxN : x ∉ F \ ({a} : Set V) := fun h => hxF h.1
    have hRsub : R ⊆ F \ ({a} : Set V) := by
      intro b hb
      exact ⟨hb.1, by aesop⟩
    exact ((hF.indep.sdiff _).insert_indep_iff_of_notMem hxN).mp hxa.indep |>.2
      (M.closure_subset_closure hRsub h)
  have hcl := Matroid.closure_insert_congr (M := M) ⟨hxcl, hxNot⟩
  by_contra hne
  have hYi : M.Indep (insert y (insert x R)) := hB.subset (by intro z hz; aesop)
  have hyN : y ∉ insert x R := by simp [R, Ne.symm hne, hyF]
  exact ((hYi.subset (Set.subset_insert _ _)).insert_indep_iff_of_notMem hyN).mp hYi |>.2
    (hcl.symm ▸ hycl)

end Exchange

section Ridge

variable {V : Type*} [Fintype V] [LinearOrder V] {M : Matroid V}

private def Supported (M : Matroid V) (B F : Finset V) : Prop :=
  (∀ b ∈ F, b ∉ B → ¬ Passive M (F : Set V) b) ∧
    ∀ d : V, (∀ b ∈ F, ¬ Passive M (F : Set V) b → d < b) →
      ∀ b ∈ B, b ∉ F → d < b

omit [Fintype V] in
private theorem ridge_exchange {F T : Finset V} {a : V}
    (hF : M.IsBase (F : Set V)) (hT : M.IsBase (T : Set V))
    (ha : a ∈ F) (hsub : F.erase a ⊆ T) (hne : T ≠ F) :
    ∃ x ∉ F, T = insert x (F.erase a) := by
  classical
  have hcard : F.card = T.card := by simpa using hF.ncard_eq_ncard_of_isBase hT
  have hs : (T \ F.erase a).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_erase_of_mem ha, ← hcard]
    have hp := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hs
  have hT' : T = insert x (F.erase a) := by
    calc
      T = T \ F.erase a ∪ F.erase a := (Finset.sdiff_union_of_subset hsub).symm
      _ = insert x (F.erase a) := by rw [hx, Finset.singleton_union]
  have hxF : x ∉ F := by
    intro hxF
    have hxnot : x ∉ F.erase a := (Finset.mem_sdiff.mp (hx ▸ Finset.mem_singleton_self x)).2
    have eq : x = a := by
      by_contra h
      exact hxnot (Finset.mem_erase.mpr ⟨h, hxF⟩)
    subst x
    exact hne (hT'.trans (Finset.insert_erase ha))
  exact ⟨x, hxF, hT'⟩

omit [Fintype V] in
private theorem support_of_exchange {B F : Finset V} {a x : V}
    (hF : M.IsBase (F : Set V)) (ha : a ∈ F)
    (hactive : ¬ Passive M (F : Set V) a)
    (hmin : ∀ b ∈ F, ¬ Passive M (F : Set V) b → a ≤ b)
    (hx : x ∉ F) (hax : a < x)
    (hT : M.IsBase ((insert x (F.erase a) : Finset V) : Set V))
    (hSupport : Supported M B (insert x (F.erase a))) :
    a ∉ B ∧ x ∈ B ∧ Supported M B F ∧
      ∀ b ∈ F, b ∉ B → b ≠ a → ¬ M.IsBase (insert x ((F : Set V) \ {b})) := by
  classical
  let T := insert x (F.erase a)
  have hTset : (T : Set V) = insert x ((F : Set V) \ {a}) := by simp [T]
  have hTbase : M.IsBase (insert x ((F : Set V) \ {a})) := hTset ▸ hT
  have haT : a ∉ T := by simp [T, ne_of_lt hax]
  have hxT : x ∈ T := Finset.mem_insert_self _ _
  have hxpass : Passive M (T : Set V) x := by
    refine ⟨a, haT, hax, ?_⟩
    convert hF using 1
    ext y
    simp only [hTset, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    by_cases hya : y = a
    · subst y
      simp [ha]
    · by_cases hyx : y = x
      · subst y
        simp [hx, hya]
      · tauto
  have hpersist (b : V) (hb : b ∈ F) (hba : b ≠ a)
      (hp : Passive M (F : Set V) b) : Passive M (T : Set V) b := by
    rw [hTset]
    exact passive_persists hF ha hb hba.symm hax hx hactive hTbase hp
  have hLater : ∀ b ∈ T, ¬ Passive M (T : Set V) b → a < b := by
    intro b hb hbp
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact (hbp hxpass).elim
    have hb' := Finset.mem_erase.mp hb
    exact lt_of_le_of_ne (hmin b hb'.2 (fun hp => hbp (hpersist b hb'.2 hb'.1 hp))) hb'.1.symm
  have haB : a ∉ B := fun h => (lt_irrefl a) (hSupport.2 a hLater a h haT)
  have hxB : x ∈ B := by
    by_contra h
    exact hSupport.1 x hxT h hxpass
  have hOld (b : V) (hb : b ∈ F) (hbB : b ∉ B) :
      ¬ Passive M (F : Set V) b := by
    by_cases hba : b = a
    · simpa [hba] using hactive
    · have hbt : b ∈ T := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hba, hb⟩)
      exact fun hp => hSupport.1 b hbt hbB (hpersist b hb hba hp)
  refine ⟨haB, hxB, ⟨hOld, ?_⟩, ?_⟩
  · intro d hd b hbB hbF
    by_cases hbx : b = x
    · exact (hd a ha hactive).trans (hbx ▸ hax)
    · have hbt : b ∉ T := by simp [T, hbx, hbF]
      exact (hd a ha hactive).trans (hSupport.2 a hLater b hbB hbt)
  · intro b hb hbB hba hswap
    have hbT : b ∈ T := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hba, hb⟩)
    have hab : a < b := lt_of_le_of_ne (hmin b hb (hOld b hb hbB)) hba.symm
    have hEq : insert a ((T : Set V) \ {b}) = insert x ((F : Set V) \ {b}) := by
      ext y
      simp only [hTset, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      have hxb : x ≠ b := fun h => hx (h ▸ hb)
      by_cases hya : y = a
      · subst y
        simp [ha, hba.symm]
      · by_cases hyb : y = b
        · subst y
          simp [hya, hxb.symm]
        · tauto
    exact hSupport.1 b hbT hbB ⟨a, haT, hab, hEq ▸ hswap⟩

private theorem higher_weight {F : Finset V} {a x : V} (ha : a ∈ F)
    (hx : x ∉ F) (hax : a < x) :
    (∑ v ∈ F, ((Fintype.orderIsoFinOfCardEq V rfl).symm v).val) <
      ∑ v ∈ insert x (F.erase a), ((Fintype.orderIsoFinOfCardEq V rfl).symm v).val := by
  let rank := (Fintype.orderIsoFinOfCardEq V rfl).symm
  have hlt : (rank a).val < (rank x).val := rank.strictMono hax
  change (∑ v ∈ F, (rank v).val) < ∑ v ∈ insert x (F.erase a), (rank v).val
  have hsum := Finset.sum_erase_add F (fun v => (rank v).val) ha
  rw [← hsum, Finset.sum_insert (fun h => hx (Finset.mem_of_mem_erase h))]
  omega

private theorem normalized_cycle_bound (M : Matroid V) (bases : Finset (Finset V))
    (hbase : ∀ F ∈ bases, M.IsBase (F : Set V)) (B : Finset V) (hB : M.Indep (B : Set V))
    (z : Finset V → ℤ) (sign : Finset V → Finset V → ℤ)
    (hunit : ∀ R T, R ⊆ T → R.card + 1 = T.card → sign R T = 1 ∨ sign R T = -1)
    (hcycle : ∀ F ∈ bases, ∀ a ∈ F,
      ∑ T ∈ bases.filter (F.erase a ⊆ ·), sign (F.erase a) T * z T = 0)
    (hnorm : ∀ F ∈ bases, (∀ a ∈ F, Passive M (F : Set V) a) →
      z F = if F = B then 1 else 0)
    (F : Finset V) (hF : F ∈ bases) : -1 ≤ z F ∧ z F ≤ 1 := by
  classical
  let score (S : Finset V) := ∑ v ∈ S, ((Fintype.orderIsoFinOfCardEq V rfl).symm v).val
  let remaining (S : Finset V) := score Finset.univ - score S
  have support_bound : ∀ F ∈ bases,
      (z F ≠ 0 → Supported M B F) ∧ (-1 ≤ z F ∧ z F ≤ 1) := by
    intro F
    induction F using (measure remaining).wf.induction with
    | h F ih =>
      intro hF
      by_cases hcrit : ∀ a ∈ F, Passive M (F : Set V) a
      · by_cases he : F = B
        · subst F
          exact ⟨fun _ => ⟨fun _ hb hn => (hn hb).elim, fun _ _ _ hb hn => (hn hb).elim⟩,
            by simp [hnorm B hF hcrit]⟩
        · have hz : z F = 0 := by simpa [he] using hnorm F hF hcrit
          exact ⟨fun hn => (hn hz).elim, by simp [hz]⟩
      let active := F.filter (fun a => ¬ Passive M (F : Set V) a)
      have hnonempty : active.Nonempty := by
        push Not at hcrit
        exact hcrit.imp (fun a ha => Finset.mem_filter.mpr ha)
      let a := active.min' hnonempty
      have ha' := Finset.mem_filter.mp (Finset.min'_mem active hnonempty)
      have ha : a ∈ F := ha'.1
      have hactive : ¬ Passive M (F : Set V) a := ha'.2
      have hmin (b : V) (hb : b ∈ F) (hbp : ¬ Passive M (F : Set V) b) : a ≤ b :=
        Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hbp⟩)
      let R := F.erase a
      let row := bases.filter (R ⊆ ·)
      have hFr : F ∈ row := Finset.mem_filter.mpr ⟨hF, Finset.erase_subset _ _⟩
      have hsize : R.card + 1 = F.card := Finset.card_erase_add_one ha
      have hFunit := hunit R F (Finset.erase_subset _ _) hsize
      have hrow := hcycle F hF a ha
      change ∑ T ∈ row, sign R T * z T = 0 at hrow
      have next (T : Finset V) (hT : T ∈ row.erase F) (hz : z T ≠ 0) :
          ∃ x : V, x ∉ F ∧ x ∈ B ∧ T = insert x R ∧ a ∉ B ∧ Supported M B F ∧
            (∀ b ∈ F, b ∉ B → b ≠ a → ¬ M.IsBase (insert x ((F : Set V) \ {b}))) ∧
            (-1 ≤ z T ∧ z T ≤ 1) := by
        obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hT
        obtain ⟨hTb, hTsub⟩ := Finset.mem_filter.mp hm
        obtain ⟨x, hx, hEq⟩ := ridge_exchange (hbase F hF) (hbase T hTb) ha hTsub hne
        have hTbase : M.IsBase (insert x ((F : Set V) \ {a})) := by
          simpa [hEq] using hbase T hTb
        have hax : a < x := by
          refine lt_of_le_of_ne (le_of_not_gt (fun hl => hactive ⟨x, hx, hl, hTbase⟩)) ?_
          exact fun he => hx (he ▸ ha)
        have hlt : score F < score T := by rw [hEq]; exact higher_weight ha hx hax
        have hle : score T ≤ score Finset.univ :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ T)
        have hmeasure : remaining T < remaining F := by dsimp [remaining]; omega
        have hi := ih T hmeasure hTb
        have hsupport := hi.1 hz
        rw [hEq] at hsupport
        have hTbase' : M.IsBase ((insert x (F.erase a) : Finset V) : Set V) :=
          hEq ▸ hbase _ hTb
        obtain ⟨haB, hxB, hSup, hOnly⟩ :=
          support_of_exchange (hbase F hF) ha hactive hmin hx hax hTbase' hsupport
        exact ⟨x, hx, hxB, hEq, haB, hSup, hOnly, hi.2⟩
      rw [← Finset.sum_erase_add _ _ hFr] at hrow
      by_cases hex : ∃ T ∈ row.erase F, z T ≠ 0
      · obtain ⟨T, hTr, hzT⟩ := hex
        obtain ⟨x, hx, hxB, hTx, haB, hSup, hOnly, hBound⟩ := next T hTr hzT
        have hTb := (Finset.mem_filter.mp (Finset.mem_erase.mp hTr).2).1
        have hTsub := (Finset.mem_filter.mp (Finset.mem_erase.mp hTr).2).2
        have hTcard : F.card = T.card := by
          simpa using (hbase F hF).ncard_eq_ncard_of_isBase (hbase T hTb)
        have hTunit := hunit R T hTsub (hsize.trans hTcard)
        have hTxset : M.IsBase (insert x ((F : Set V) \ {a})) := by
          simpa [hTx, R] using hbase T hTb
        have hxG : x ∈ M.E := hTxset.subset_ground (Set.mem_insert _ _)
        have hs : ∑ U ∈ row.erase F, sign R U * z U = sign R T * z T := by
          apply Finset.sum_eq_single T
          · intro U hUr hne
            by_cases hzU : z U = 0
            · simp [hzU]
            · obtain ⟨y, hy, hyB, hUy, _, _, hOnly', _⟩ := next U hUr hzU
              have hybase : M.IsBase (insert y ((F : Set V) \ {a})) := by
                have hUb := (Finset.mem_filter.mp (Finset.mem_erase.mp hUr).2).1
                simpa [hUy, R] using hbase U hUb
              have hyG : y ∈ M.E := hybase.subset_ground (Set.mem_insert _ _)
              have he : x = y :=
                unique_admissible_insert (hbase F hF) hB
                  ha haB hx hy hxB hyB hxG hyG hTxset hOnly hOnly'
              exact (hne (hUy.trans (he ▸ hTx.symm))).elim
          · exact fun hn => (hn hTr).elim
        rw [hs] at hrow
        refine ⟨fun _ => hSup, ?_⟩
        rcases hFunit with hsignF | hsignF <;> rcases hTunit with hsignT | hsignT <;>
          rw [hsignF, hsignT] at hrow <;> omega
      · have hs : ∑ T ∈ row.erase F, sign R T * z T = 0 := by
          apply Finset.sum_eq_zero
          intro T hT
          simp [show z T = 0 from not_not.mp (fun h => hex ⟨T, hT, h⟩)]
        rw [hs, zero_add] at hrow
        have hz : z F = 0 := by
          rcases hFunit with hsign | hsign <;> rw [hsign] at hrow <;> omega
        exact ⟨fun h => (h hz).elim, by simp [hz]⟩
  exact (support_bound F hF).2

end Ridge

section Signed

open D5.S3.TotalVariation.FairBiasMatching
open D5.S3.TotalVariation.FairBiasRestriction
open D5.S3.TotalVariation.FairBiasShelling
open D5.S3.TotalVariation.FairBiasChainContraction

variable {A L : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
  [Fintype L] [LinearOrder (L × Bool)]
variable {c : L → A}

noncomputable section

private def extendFace (f : Face c → ℤ) (S : Finset (L × Bool)) : ℤ := by
  classical
  exact if h : S ∈ augmentedFaces c then f ⟨S, h⟩ else 0

omit [Module (ZMod 2) A] [Finite A] [LinearOrder (L × Bool)] in
private theorem extendFace_apply (f : Face c → ℤ) (s : Face c) :
    extendFace f s.val = f s := by
  classical
  simp [extendFace, s.property]

private def extendedBoundary (c : L → A) (R T : Finset (L × Bool)) : ℤ := by
  classical
  exact if hR : R ∈ augmentedFaces c then
    if hT : T ∈ augmentedFaces c then boundary c ⟨R, hR⟩ ⟨T, hT⟩ else 1
  else 1

private theorem signed_ridge_equation (z : Face c → ℤ)
    (hTop : ∀ S : Face c, S.val ∉ facets c → z S = 0)
    (hCycle : ∀ R : Face c, ∑ T : Face c, boundary c R T * z T = 0)
    (F : Finset (L × Bool)) (hF : F ∈ facets c) (a : L × Bool) (ha : a ∈ F) :
    ∑ T ∈ (facets c).filter (F.erase a ⊆ ·),
      extendedBoundary c (F.erase a) T * extendFace z T = 0 := by
  classical
  letI : DecidableEq (L × Bool) := LinearOrder.toDecidableEq
  let R := F.erase a
  let r : Face c := ⟨F.erase a, augmented_of_subset_facet c hF (Finset.erase_subset _ _)⟩
  let faces : Finset (Face c) := Finset.univ.filter (fun T => T.val ∈ facets c ∧ R ⊆ T.val)
  have hsum :
      ∑ T ∈ (facets c).filter (F.erase a ⊆ ·), extendedBoundary c (F.erase a) T * extendFace z T =
        ∑ t ∈ faces, boundary c r t * z t := by
    symm
    apply Finset.sum_bij (fun t _ => t.val)
    · intro t ht
      have ht' := (Finset.mem_filter.mp ht).2
      exact Finset.mem_filter.mpr ht'
    · intro t₁ _ t₂ _ he
      exact Subtype.ext he
    · intro T ht
      have ht' := Finset.mem_filter.mp ht
      have hT := augmented_of_subset_facet c ht'.1 Finset.Subset.rfl
      exact ⟨⟨T, hT⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩, rfl⟩
    · intro t _
      have hR : F.erase a ∈ augmentedFaces c := r.property
      simp only [extendedBoundary, extendFace, hR, t.property, dite_true]
      rfl
  rw [hsum]
  change ∑ t ∈ Finset.univ.filter (fun T : Face c => T.val ∈ facets c ∧ R ⊆ T.val),
    boundary c r t * z t = 0
  rw [Finset.sum_filter]
  calc
    _ = ∑ t : Face c, boundary c r t * z t := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val ∈ facets c ∧ R ⊆ t.val
      · simp [ht]
      · rw [if_neg ht]
        by_cases hfacet : t.val ∈ facets c
        · have hzero : boundary c r t = 0 := by
            by_contra hn
            exact ht ⟨hfacet, (cover_of_boundary_ne_zero hn).1⟩
          simp [hzero]
        · simp [hTop t hfacet]
    _ = 0 := hCycle r

/-- Normalize a top integral cycle on the full-restriction facets. Each signed
face then has coefficient zero, one, or minus one. -/
theorem normalized_cycle_unit_coefficients (c : L → A) (B : Face c)
    (z : Face c → ℤ)
    (hTop : ∀ S : Face c, S.val ∉ facets c → z S = 0)
    (hCycle : ∀ R : Face c, ∑ T : Face c, boundary c R T * z T = 0)
    (hNorm : ∀ S : Face c, S.val ∈ facets c → restrictionFace c S.val = S.val →
      z S = if S = B then 1 else 0)
    (S : Face c) : -1 ≤ z S ∧ z S ≤ 1 := by
  classical
  by_cases hS : S.val ∈ facets c
  · obtain ⟨F, hF, hFirst⟩ := exists_first_facet c ⟨S.val, hS⟩ B.property
    have hB : (signedMatroid c).Indep (B.val : Set (L × Bool)) :=
      ((facet_iff_base c F).mp (mem_facets.mp hF)).2.indep.subset hFirst.1
    have hBound := normalized_cycle_bound (signedMatroid c) (facets c)
        (fun F hF => ((facet_iff_base c F).mp (mem_facets.mp hF)).2)
        B.val hB (extendFace z) (extendedBoundary c) ?_ ?_ ?_ S.val hS
    · simpa only [extendFace_apply] using hBound
    · intro R T hsub hsize
      by_cases hR : R ∈ augmentedFaces c
      · by_cases hT : T ∈ augmentedFaces c
        · simp only [extendedBoundary, hR, hT, dite_true]
          exact mul_self_eq_one_iff.mp
            (boundary_unit_of_cover (c := c) (s := ⟨R, hR⟩) (t := ⟨T, hT⟩) ⟨hsub, hsize.symm⟩)
        · simp [extendedBoundary, hR, hT]
      · simp [extendedBoundary, hR]
    · exact signed_ridge_equation z hTop hCycle
    · intro F hF hpassive
      have hcritical : restrictionFace c F = F := by
        apply Finset.Subset.antisymm (Finset.filter_subset _ _)
        intro a ha
        obtain ⟨x, hx, hxa, hX⟩ := hpassive a ha
        let X := insert x (F.erase a)
        have hXF : X ∈ facets c := by
          apply mem_facets.mpr
          refine (facet_iff_base c X).mpr ⟨⟨x, Finset.mem_insert_self _ _⟩, ?_⟩
          simpa [X] using hX
        apply Finset.mem_filter.mpr
        refine ⟨ha, X, hXF, ?_, Finset.subset_insert _ _⟩
        apply lexBefore_iff.mpr
        refine ⟨x, Finset.mem_insert_self _ _, hx, ?_⟩
        intro y hy hyX
        have he : y = a := by
          by_contra hne
          exact hyX (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hy⟩))
        simpa [he] using hxa
      have hFaug := augmented_of_subset_facet c hF Finset.Subset.rfl
      let f : Face c := ⟨F, hFaug⟩
      have hvalue : extendFace z F = z f := extendFace_apply z f
      rw [hvalue, hNorm f hF hcritical]
      by_cases hEq : F = B.val
      · have hf : f = B := Subtype.ext hEq
        simp [hf, hEq]
      · have hf : f ≠ B := fun he => hEq (congrArg Subtype.val he)
        simp [hf, hEq]
  · simp [hTop S hS]

end

end Signed

end D5.S3.TotalVariation.FairBiasCycleCoefficients
