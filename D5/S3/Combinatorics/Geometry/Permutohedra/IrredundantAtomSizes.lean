/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Irredundant atom joins realize every size from two through the face rank. -/
import D5.S3.Combinatorics.Geometry.Permutohedra.FaceFlags
import D5.S3.Combinatorics.Geometry.Permutohedra.PrefixExchanges

/-! The size spectrum of irredundant atom joins in the permutohedron face lattice. -/

namespace Rossi
open Finset D5.S3.Combinatorics.Graph.PrefixHamming

private theorem spectrum_construct {n k : ℕ} (hn : 3 ≤ n) (x : CutChain n)
    (hk : 2 ≤ k) (hkr : (k : ℤ) ≤ rank (x : Face n)) :
    ∃ A : Finset (Face n), A.card = k ∧ (∀ a ∈ A, IsAtom a) ∧
      A.sup id = (x : Face n) ∧ ∀ B : Finset (Face n), B ⊂ A → B.sup id < (x : Face n) := by
  classical
  letI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨p, hp⟩ := exists_flag_extension x
  have hcount : k ≤ Fintype.card ↥(free x) := by
    rw [Fintype.card_coe]
    have := card_free (by omega) x
    omega
  obtain ⟨embed⟩ : Nonempty (Fin k ↪ ↥(free x)) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hcount)
  let label : ↥(free x) → Fin k := Function.invFun embed
  have hlabel : Function.Surjective label := Function.invFun_surjective embed.injective
  let ds (i : Fin k) : List (Rank n) :=
    ((free x).attach.filter fun t => label t = i).toList.map Subtype.val
  have nodup (i : Fin k) : (ds i).Nodup :=
    (Finset.nodup_toList _).map Subtype.val_injective
  have mem_ds (d : Rank n) (i : Fin k) : d ∈ ds i ↔ ∃ h : d ∈ free x, label ⟨d, h⟩ = i := by
    simp only [ds, List.mem_map, Finset.mem_toList, mem_filter, mem_attach, true_and]
    constructor
    · rintro ⟨⟨t, ht⟩, hh, rfl⟩
      exact ⟨ht, hh⟩
    · rintro ⟨hd, hh⟩
      exact ⟨⟨d, hd⟩, hh, rfl⟩
  let q (i : Fin k) := batch p (ds i)
  let f (i : Fin k) := atom (q i)
  have changed (i : Fin k) (d : Rank n) :
      prefixSet (q i) d.1.val ≠ prefixSet p d.1.val ↔
        ∃ h : d ∈ free x, label ⟨d, h⟩ = i :=
    (batch_prefix_ne_iff p (ds i) (nodup i) d).trans (mem_ds d i)
  have eq_base (t : ↥(free x)) {i : Fin k} (hi : label t ≠ i) :
      prefixSet (q i) t.1.1.val = prefixSet p t.1.1.val := by
    apply not_ne_iff.mp
    intro h
    obtain ⟨_, hh⟩ := (changed i t.1).1 h
    exact hi hh
  have mem_fixed (i : Fin k) : x.cuts ⊆ (flag (q i)).cuts := by
    intro c hc
    let d : Rank n := ⟨⟨c.card, (x.proper c hc).2⟩, (x.proper c hc).1⟩
    have he : prefixSet p d.1.val = c := (mem_flag p d.1.isLt d.2).1 (hp hc)
    have hnf : d ∉ free x := (prefix_mem_cuts_iff hp d).1 (he.symm ▸ hc)
    have hq : prefixSet (q i) d.1.val = prefixSet p d.1.val :=
      not_ne_iff.mp (fun h => let ⟨hd, _⟩ := (changed i d).1 h; hnf hd)
    exact (hq.trans he) ▸ prefix_mem_flag (q i) d
  have finj : Function.Injective f := by
    intro i j hij
    by_contra hne
    obtain ⟨t, ht⟩ := hlabel i
    have hi := (changed i t.1).2 ⟨t.2, ht⟩
    have hj := eq_base t (ht ▸ hne)
    have he : flag (q i) = flag (q j) := WithBot.coe_injective hij
    have hmem : prefixSet (q i) t.1.1.val ∈ (flag (q j)).cuts :=
      he ▸ prefix_mem_flag (q i) t.1
    have hcard := prefix_card (q i) t.1.1.isLt
    have eq := (mem_flag (q j) (by rw [hcard]; exact t.1.1.isLt)
      (by rw [hcard]; exact t.1.2)).1 hmem
    rw [hcard, hj] at eq
    exact hi eq.symm
  let A : Finset (Face n) := univ.image f
  have hA (a : Face n) : a ∈ A ↔ ∃ i, f i = a := by simp [A]
  have hAb : ∃ a ∈ A, a ≠ ⊥ := by
    let i : Fin k := ⟨0, by omega⟩
    exact ⟨f i, (hA _).2 ⟨i, rfl⟩, WithBot.coe_ne_bot⟩
  have hAtom (a : Face n) (ha : a ∈ A) : IsAtom a := by
    obtain ⟨i, rfl⟩ := (hA a).1 ha
    exact atom_isAtom (q i)
  have hj : A.sup id = (x : Face n) := by
    apply join_eq hAb
    intro c
    constructor
    · intro hc y hy
      obtain ⟨i, he⟩ := (hA _).1 hy
      have eq : flag (q i) = y := WithBot.coe_injective he
      exact eq ▸ mem_fixed i hc
    · intro h
      obtain ⟨a, ha, _⟩ := hAb
      obtain ⟨i, rfl⟩ := (hA a).1 ha
      obtain ⟨hpos, hlt⟩ := (flag (q i)).proper c (h _ ha)
      let d : Rank n := ⟨⟨c.card, hlt⟩, hpos⟩
      by_cases hf : d ∈ free x
      · let t : ↥(free x) := ⟨d, hf⟩
        obtain ⟨j, hj⟩ := exists_ne (label t)
        have hi := (changed (label t) d).2 ⟨hf, rfl⟩
        have he (l : Fin k) : prefixSet (q l) c.card = c :=
          (mem_flag (q l) hlt hpos).1 (h _ ((hA _).2 ⟨l, rfl⟩))
        have hbase := eq_base t hj.symm
        change prefixSet (q j) c.card = prefixSet p c.card at hbase
        exact (hi ((he _).trans ((he j).symm.trans hbase))).elim
      · have hc := (prefix_mem_cuts_iff hp d).2 hf
        have hq := not_ne_iff.mp (fun hq =>
          let ⟨hm, _⟩ := (changed i d).1 hq; hf hm)
        have hqi := (mem_flag (q i) hlt hpos).1 (h _ ha)
        have eq : prefixSet p c.card = c := hq.symm.trans hqi
        exact eq ▸ hc
  refine ⟨A, by simp [A, card_image_of_injective _ finj], hAtom, hj, ?_⟩
  apply proper_lt_of_erase_lt
  intro a ha
  obtain ⟨i, rfl⟩ := (hA _).1 ha
  obtain ⟨t, ht⟩ := hlabel i
  apply strict_of_extra_cut (show (A.erase (f i)).sup id ≤ (x : Face n) from
    hj ▸ Finset.sup_mono (Finset.erase_subset _ _))
    (fun h => (prefix_mem_cuts_iff hp t.1).1 h t.2)
  intro y hy
  obtain ⟨j, he⟩ := (hA _).1 (mem_of_mem_erase hy)
  have hne : label t ≠ j := by
    intro h
    exact (mem_erase.mp hy).1 (by rw [← he, ← h, ht])
  have hmem : prefixSet p t.1.1.val ∈ (flag (q j)).cuts :=
    (eq_base t hne) ▸ prefix_mem_flag (q j) t.1
  exact (WithBot.coe_injective he) ▸ hmem

private theorem spectrum_bound {n : ℕ} (hn : 3 ≤ n) (x : CutChain n)
    (hx : 2 ≤ rank (x : Face n)) (A : Finset (Face n))
    (hAtom : ∀ a ∈ A, IsAtom a) (hjoin : A.sup id = (x : Face n))
    (hmin : ∀ B : Finset (Face n), B ⊂ A → B.sup id < (x : Face n)) :
    2 ≤ A.card ∧ (A.card : ℤ) ≤ rank (x : Face n) := by
  classical
  have hl : 2 ≤ A.card := by
    by_contra! h
    have hc : A.card = 0 ∨ A.card = 1 := by omega
    rcases hc with hc | hc
    · rw [card_eq_zero.mp hc, Finset.sup_empty] at hjoin
      exact WithBot.coe_ne_bot hjoin.symm
    · obtain ⟨a, rfl⟩ := card_eq_one.mp hc
      rw [Finset.sup_singleton, id_eq] at hjoin
      obtain ⟨p, hp⟩ := (isAtom_iff_flag a).1 (hAtom _ (mem_singleton_self _))
      have he : x = flag p := WithBot.coe_injective (hjoin.symm.trans hp)
      subst x
      have hcard : (flag p).cuts.card = n - 1 := by
        change (univ.image fun d : Rank n => prefixSet p d.1.val).card = _
        rw [card_image_of_injective, card_univ, card_rank_type]
        intro d e hde
        apply Subtype.ext
        apply Fin.ext
        simpa only [prefix_card p d.1.isLt, prefix_card p e.1.isLt]
          using congrArg Finset.card hde
      change (2 : ℤ) ≤ (n : ℤ) - 1 - (flag p).cuts.card at hx
      omega
  refine ⟨hl, ?_⟩
  by_cases he : A.card = 2
  · simpa [he] using hx
  have h3 : 2 < A.card := by omega
  have above (a : ↥A) : ∃ y : CutChain n, a.1 = (y : Face n) := by
    obtain ⟨p, hp⟩ := (isAtom_iff_flag a.1).1 (hAtom a.1 a.2)
    exact ⟨flag p, hp⟩
  choose C hC using above
  have private_cut (a : ↥A) : ∃ c : Finset (Fin n),
      (0 < c.card ∧ c.card < n) ∧ c ∉ x.cuts ∧ c ∉ (C a).cuts ∧
      ∀ b : ↥A, b ≠ a → c ∈ (C b).cuts := by
    let B := A.erase a.1
    have hB : B ⊂ A := erase_ssubset a.2
    have hlt := hmin B hB
    have hbn : B.Nonempty := by
      apply card_pos.mp
      show 0 < (A.erase a.1).card
      rw [card_erase_of_mem a.2]
      omega
    have hne : B.sup id ≠ ⊥ := by
      obtain ⟨b, hb⟩ := hbn
      intro he
      exact (hAtom b (mem_of_mem_erase hb)).1 (le_bot_iff.mp (he ▸ Finset.le_sup (f := id) hb))
    cases hsup : B.sup id using WithBot.recBotCoe
    · exact (hne hsup).elim
    rename_i z
    rw [hsup] at hlt
    have hzle : z ≤ x := WithBot.coe_le_coe.mp hlt.le
    have hsub : x.cuts ⊆ z.cuts := hzle
    have hs : x.cuts ⊂ z.cuts := Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun he =>
      hlt.ne (congrArg (fun w : CutChain n => (w : Face n)) (CutChain.ext_cuts he.symm))⟩
    obtain ⟨c, hcz, hcx⟩ := (ssubset_iff_of_subset hsub).1 hs
    have hall (b : ↥A) (hb : b ≠ a) : c ∈ (C b).cuts := by
      apply (sup_cuts hsup c).1 hcz
      rw [← hC b]
      exact mem_erase.2 ⟨fun he => hb (Subtype.ext he), b.2⟩
    refine ⟨c, z.proper c hcz, hcx, ?_, hall⟩
    intro hca
    apply hcx
    apply (sup_cuts hjoin c).2
    intro y hy
    let b : ↥A := ⟨(y : Face n), hy⟩
    have eq : y = C b := WithBot.coe_injective (hC b)
    rw [eq]
    by_cases he : b = a
    · simpa only [he] using hca
    · exact hall b he
  choose Q hQ using private_cut
  have rk_free (a : ↥A) :
      (⟨⟨(Q a).card, (hQ a).1.2⟩, (hQ a).1.1⟩ : Rank n) ∈ free x := by
    let t : Rank n := ⟨⟨(Q a).card, (hQ a).1.2⟩, (hQ a).1.1⟩
    change t ∈ free x
    by_contra h
    have ht : t ∈ occupied x := by simpa [free] using h
    obtain ⟨c, _, he⟩ := mem_image.mp ht
    have hc : c.1.card = (Q a).card := congrArg (fun d : Rank n => d.1.val) he
    have ha : (A.erase a.1).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem a.2]
      omega
    obtain ⟨b, hb⟩ := ha
    let b' : ↥A := ⟨b, mem_of_mem_erase hb⟩
    have hba : b' ≠ a := fun h => (mem_erase.mp hb).1 (congrArg Subtype.val h)
    have hq := (hQ a).2.2.2 b' hba
    have hcc : c.1 ∈ (C b').cuts :=
      (sup_cuts hjoin c.1).1 c.2 _ ((hC b') ▸ b'.2)
    have eq := (C b').eq_of_card_eq hcc hq hc
    exact (hQ a).2.1 (eq ▸ c.2)
  let f (a : ↥A) : ↥(free x) := ⟨⟨⟨(Q a).card, (hQ a).1.2⟩, (hQ a).1.1⟩, rk_free a⟩
  have hinj : Function.Injective f := by
    intro a b he
    by_contra hab
    have hcard : (Q a).card = (Q b).card :=
      congrArg (fun d : ↥(free x) => d.1.1.val) he
    have hsmall : ({a.1, b.1} : Finset (Face n)).card < A.card :=
      lt_of_le_of_lt (by simpa using (card_insert_le a.1 ({b.1} : Finset (Face n)))) h3
    obtain ⟨c, hc, hnot⟩ := exists_mem_notMem_of_card_lt_card hsmall
    let c' : ↥A := ⟨c, hc⟩
    have hca : c' ≠ a := fun h => hnot (mem_insert.mpr (Or.inl (congrArg Subtype.val h)))
    have hcb : c' ≠ b := fun h => hnot (mem_insert.mpr (Or.inr (mem_singleton.mpr (congrArg Subtype.val h))))
    have hqa := (hQ a).2.2.2 c' hca
    have hqb := (hQ b).2.2.2 c' hcb
    have eq := (C c').eq_of_card_eq hqa hqb hcard
    exact (hQ b).2.2.1 (eq ▸ (hQ a).2.2.2 b (fun h => hab h.symm))
  have hnat : A.card ≤ (free x).card := card_le_card_of_injective hinj
  rw [← card_free (by omega) x]
  exact_mod_cast hnat

theorem exact_spectrum (n : ℕ) (hn : 3 ≤ n) (x : Face n)
    (hx : 2 ≤ rank x) (k : ℕ) :
    (∃ A : Finset (Face n), A.card = k ∧ (∀ a ∈ A, IsAtom a) ∧
      A.sup id = x ∧ ∀ B : Finset (Face n), B ⊂ A → B.sup id < x) ↔
    2 ≤ k ∧ (k : ℤ) ≤ rank x := by
  cases x using WithBot.recBotCoe
  · change (2 : ℤ) ≤ -1 at hx
    omega
  rename_i x
  constructor
  · rintro ⟨A, rfl, ha, hj, hm⟩
    exact spectrum_bound hn x hx A ha hj hm
  · exact fun h => spectrum_construct hn x h.1 h.2

end Rossi
