/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection
   mirror-E: none(waiver:royal-permutation-dyck-bijection)
   anchors: []
   utility: none
   digest: Gives the explicit permutation-Dyck equivalence for nonnesting doubled words. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalShape

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBijection

open scoped symmDiff
open DyckStep

open DyckStep NonnestingBasicRoyalEncoding NonnestingBasicRoyalShape

local notation "toggle" =>
  (fun (active : Finset ℕ) (letter : ℕ) => active ∆ Singleton.singleton letter)
def royalPairs (n : ℕ) : Type :=
  {pd : List ℕ × DyckWord // pd.1.Perm (List.range' 1 n) ∧
    pd.1.length = pd.2.semilength}
def royalEncoding (n : ℕ) : royalPairs n ≃
    {w : List ℕ // w ∈ NonnestingDefs.avoiders n []} := by
  classical
  have foldl_toggle_parity (s : Finset ℕ) (w : List ℕ) (a : ℕ) :
      a ∈ w.foldl toggle s ↔
        if w.count a % 2 = 0 then a ∈ s else a ∉ s := by
    have toggle_eq (active : Finset ℕ) (letter : ℕ) :
        toggle active letter =
          if letter ∈ active then active.erase letter else insert letter active := by
      ext value
      by_cases present : letter ∈ active <;>
        simp [Finset.mem_symmDiff, present] <;> grind
    have mem_toggle_iff (s : Finset ℕ) (a b : ℕ) :
        a ∈ toggle s b ↔ if a = b then a ∉ s else a ∈ s := by
      by_cases hab : a = b
      · subst b
        by_cases ha : a ∈ s <;> simp [toggle_eq, ha]
      · by_cases hb : b ∈ s <;> simp [toggle_eq, hab, hb]
    induction w generalizing s with
    | nil => simp
    | cons b w ih =>
      simp only [List.foldl_cons, ih, mem_toggle_iff]
      by_cases hab : a = b
      · subst b
        by_cases hpar : w.count a % 2 = 0
        · have hnext : (w.count a + 1) % 2 = 1 := by omega
          simp [hpar, hnext]
        · have hnext : (w.count a + 1) % 2 = 0 := by
            have hbound := Nat.mod_lt (w.count a) (by omega : 0 < 2); omega
          simp [hpar, hnext]
      · simp [hab, Ne.symm hab]
  have scan_getElem? (s : Finset ℕ) (w : List ℕ) (i : ℕ) :
      (scan s w)[i]? =
        (w[i]?).map (fun a => if a ∈ (w.take i).foldl toggle s then D else U) := by
    induction w generalizing s i with
    | nil => simp [scan]
    | cons b w ih =>
      cases i with
      | zero => by_cases h : b ∈ s <;> simp [scan, h]
      | succ i => by_cases h : b ∈ s <;> simp [scan, h, ih] <;> rfl
  have scan_length (s : Finset ℕ) (w : List ℕ) : (scan s w).length = w.length := by
    induction w generalizing s with
    | nil => rfl
    | cons a w ih =>
      by_cases h : a ∈ s <;> simp [scan, h, ih]
  have scan_append (s : Finset ℕ) (u v : List ℕ) :
      scan s (u ++ v) = scan s u ++ scan (u.foldl toggle s) v := by
    induction u generalizing s with
    | nil => simp [scan]
    | cons a u ih =>
      by_cases h : a ∈ s <;> simp [scan, h, ih, List.foldl_cons]
  have select_append (t : DyckStep) (d e : List DyckStep) (u v : List ℕ)
      (h : d.length = u.length) :
      select t (d ++ e) (u ++ v) = select t d u ++ select t e v := by
    induction d generalizing u with
    | nil =>
      have : u = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm); subst u; simp [select]
    | cons x d ih =>
      cases u with
      | nil => simp at h
      | cons a u =>
        have ht : d.length = u.length := by simpa using h
        by_cases hx : x = t <;> simp [select, hx, ih u ht]
  have select_length (t : DyckStep) (d : List DyckStep) (w : List ℕ)
      (h : d.length = w.length) : (select t d w).length = d.count t := by
    induction d generalizing w with
    | nil =>
      have : w = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm); subst w; simp [select]
    | cons x d ih =>
      cases w with
      | nil => simp at h
      | cons a w =>
        have ht : d.length = w.length := by simpa using h
        by_cases hx : x = t <;> simp [select, hx, ih w ht]
  have tagged_select_sublist (t : DyckStep) (d : List DyckStep) (w : List ℕ) :
      List.Sublist ((select t d w).map (t, ·)) (d.zip w) := by
    induction d generalizing w with
    | nil => simp [select]
    | cons x d ih =>
      cases w with
      | nil => simp [select]
      | cons a w =>
        by_cases hx : x = t
        · subst x
          simpa [select] using (ih w).cons_cons (t, a)
        · simpa [select, hx] using (ih w).cons (x, a)
  have weave_exists_of_counts (p q : List ℕ) (d : List DyckStep)
      (hp : p.length = d.count U) (hq : q.length = d.count D) :
      ∃ w, weave p q d = some w := by
    induction d generalizing p q with
    | nil =>
      have hp0 : p = [] := List.eq_nil_of_length_eq_zero (by simpa using hp)
      have hq0 : q = [] := List.eq_nil_of_length_eq_zero (by simpa using hq)
      subst p; subst q; exact ⟨[], rfl⟩
    | cons s d ih =>
      cases s with
      | U =>
        cases p with
        | nil => simp at hp
        | cons a p =>
          have hp' : p.length = d.count U := by simpa using hp
          have hq' : q.length = d.count D := by simpa using hq
          obtain ⟨w, hw⟩ := ih p q hp' hq'
          exact ⟨a :: w, by simp [weave, hw]⟩
      | D =>
        cases q with
        | nil => simp at hq
        | cons a q =>
          have hp' : p.length = d.count U := by simpa using hp
          have hq' : q.length = d.count D := by simpa using hq
          obtain ⟨w, hw⟩ := ih p q hp' hq'
          exact ⟨a :: w, by simp [weave, hw]⟩
  have weave_perm (p q : List ℕ) (d : List DyckStep) (w : List ℕ)
      (hw : weave p q d = some w) : w.Perm (p ++ q) := by
    induction d generalizing p q w with
    | nil =>
      cases p with
      | nil =>
        cases q with
        | nil => simpa [weave] using hw.symm
        | cons a q => simp [weave] at hw
      | cons a p => simp [weave] at hw
    | cons s d ih =>
      cases s with
      | U =>
        cases p with
        | nil => simp [weave] at hw
        | cons a p =>
          cases h : weave p q d with
          | none => simp [weave, h] at hw
          | some v =>
            have heq : w = a :: v := by simpa [weave, h] using hw.symm
            subst w
            simpa using (ih p q v h).cons a
      | D =>
        cases q with
        | nil => simp [weave] at hw
        | cons a q =>
          cases h : weave p q d with
          | none => simp [weave, h] at hw
          | some v =>
            have heq : w = a :: v := by simpa [weave, h] using hw.symm
            subst w; exact ((ih p q v h).cons a).trans (List.perm_middle.symm)
  have weave_scan_active (r p : List ℕ) (d : List DyckStep) (w : List ℕ)
      (hnodup : (r ++ p).Nodup)
      (hprefix : ∀ i, (d.take i).count D ≤ r.length + (d.take i).count U)
      (hw : weave p (r ++ p) d = some w) :
      scan r.toFinset w = d := by
    have toggle_eq (active : Finset ℕ) (letter : ℕ) :
        toggle active letter =
          if letter ∈ active then active.erase letter else insert letter active := by
      ext value
      by_cases present : letter ∈ active <;>
        simp [Finset.mem_symmDiff, present] <;> grind
    induction d generalizing r p w with
    | nil =>
      cases p with
      | nil =>
        cases r with
        | nil =>
          have : w = [] := by simpa [weave] using hw.symm
          subst w; rfl
        | cons a r => simp [weave] at hw
      | cons a p => simp [weave] at hw
    | cons t d ih =>
      cases t with
      | U =>
        cases p with
        | nil =>
          cases r <;> simp [weave] at hw
        | cons a p =>
          have ha : a ∉ r := by
            have h := (List.nodup_append.mp hnodup).2.2; intro ham; exact (h a ham a (by simp)) rfl
          have hnodup' : ((r ++ [a]) ++ p).Nodup := by
            simpa [List.append_assoc] using hnodup
          have hprefix' : ∀ i, (d.take i).count D ≤
              (r ++ [a]).length + (d.take i).count U := by
            intro i; have h := hprefix (i + 1)
            simp only [List.take_succ_cons, List.count_cons, beq_iff_eq,
              reduceCtorEq, ite_false, ite_true, List.length_append,
              List.length_singleton] at h ⊢
            omega
          obtain ⟨v, hv, heq⟩ :
              ∃ v, weave p (r ++ a :: p) d = some v ∧ a :: v = w := by
            simpa [weave] using hw
          have hv' : weave p ((r ++ [a]) ++ p) d = some v := by
            simpa [List.append_assoc] using hv
          subst w
          have hstate : toggle r.toFinset a = (r ++ [a]).toFinset := by
            simp [toggle_eq, ha]
          simpa [scan, ha, hstate] using ih (r ++ [a]) p v hnodup' hprefix' hv'
      | D =>
        cases r with
        | nil =>
          have h := hprefix 1; simp at h
        | cons a r =>
          have hcons : (a :: (r ++ p)).Nodup := by simpa using hnodup
          have ha : a ∉ r := by
            intro ham; exact (List.nodup_cons.mp hcons).1 (List.mem_append.mpr (Or.inl ham))
          have hnodup' : (r ++ p).Nodup := (List.nodup_cons.mp hcons).2
          have hprefix' : ∀ i, (d.take i).count D ≤
              r.length + (d.take i).count U := by
            intro i; have h := hprefix (i + 1)
            simp only [List.take_succ_cons, List.count_cons, beq_iff_eq,
              reduceCtorEq, ite_false, ite_true, List.length_cons] at h
            omega
          obtain ⟨v, hv, heq⟩ :
              ∃ v, weave p (r ++ p) d = some v ∧ a :: v = w := by
            simpa [List.cons_append, weave] using hw
          subst w
          have hstate : toggle (a :: r).toFinset a = r.toFinset := by
            simp [toggle_eq, ha]
          simp only [scan, List.toFinset_cons, Finset.mem_insert_self, ite_true]
          have hstate' : insert a r.toFinset ∆ {a} = r.toFinset := by
            simpa only [List.toFinset_cons] using hstate
          rw [hstate']; exact congrArg (D :: ·) (ih r p v hnodup' hprefix' hv)
  have weave_select (p q : List ℕ) (d : List DyckStep) (w : List ℕ)
      (hw : weave p q d = some w) : select U d w = p ∧ select D d w = q := by
    induction d generalizing p q w with
    | nil =>
      cases p with
      | nil =>
        cases q with
        | nil =>
          have : w = [] := by simpa [weave] using hw.symm
          subst w; simp [select]
        | cons a q => simp [weave] at hw
      | cons a p => simp [weave] at hw
    | cons s d ih =>
      cases s with
      | U =>
        cases p with
        | nil => simp [weave] at hw
        | cons a p =>
          cases h : weave p q d with
          | none => simp [weave, h] at hw
          | some v =>
            have heq : w = a :: v := by simpa [weave, h] using hw.symm
            subst w
            obtain ⟨hu, hd⟩ := ih p q v h
            simp [select, hu, hd]
      | D =>
        cases q with
        | nil => simp [weave] at hw
        | cons a q =>
          cases h : weave p q d with
          | none => simp [weave, h] at hw
          | some v =>
            have heq : w = a :: v := by simpa [weave, h] using hw.symm
            subst w
            obtain ⟨hu, hd⟩ := ih p q v h
            simp [select, hu, hd]
  have weave_select_inverse (d : List DyckStep) (w : List ℕ)
      (hlen : d.length = w.length) :
      weave (select U d w) (select D d w) d = some w := by
    induction d generalizing w with
    | nil =>
      have : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm); subst w; rfl
    | cons s d ih =>
      cases w with
      | nil => simp at hlen
      | cons a w =>
        have htail : d.length = w.length := by simpa using hlen
        cases s <;> simp [select, weave, ih w htail]
  have select_sublist (t : DyckStep) (d : List DyckStep) (w : List ℕ) :
      List.Sublist (select t d w) w := by
    induction d generalizing w with
    | nil => simp [select]
    | cons x d ih =>
      cases w with
      | nil => simp [select]
      | cons a w =>
        by_cases hx : x = t
        · simpa [select, hx] using (ih w).cons_cons a
        · simpa [select, hx] using (ih w).cons a
  have toggle_eq (active : Finset ℕ) (letter : ℕ) :
      toggle active letter =
        if letter ∈ active then active.erase letter else insert letter active := by
    ext value
    by_cases present : letter ∈ active <;>
      simp [Finset.mem_symmDiff, present] <;> grind
  have scan_encode (p : List ℕ) (d : DyckWord)
      (hp : p.Nodup) (hlen : p.length = d.semilength) :
      scan ∅ ((weave p p d.toList).getD []) = d.toList := by
    have hU : p.length = d.toList.count U := by
      simpa [DyckWord.semilength] using hlen
    obtain ⟨w, hw⟩ := weave_exists_of_counts p p d.toList hU
      (hU.trans d.count_U_eq_count_D)
    have hprefix : ∀ i, (d.toList.take i).count D ≤
        ([] : List ℕ).length + (d.toList.take i).count U := by
      intro i
      simpa using d.count_D_le_count_U i
    have hscan := weave_scan_active [] p d.toList w (by simpa using hp) hprefix
      (by simpa using hw)
    simpa [hw] using hscan
  have doubled_concat_perm (p : List ℕ) :
      (p ++ p).Perm (p.flatMap fun a => [a, a]) := by
    induction p with
    | nil => simp
    | cons a p ih =>
      have hmove : (p ++ a :: p).Perm (a :: (p ++ p)) := List.perm_middle
      simpa [List.flatMap_cons, List.cons_append] using
        (hmove.cons a).trans ((ih.cons a).cons a)
  have tagged_pair_positions (t : DyckStep) (d : List DyckStep) (w : List ℕ)
      (a b : ℕ)
      (hab : List.Sublist [(t, a), (t, b)] (d.zip w)) :
      ∃ i j : ℕ, i < j ∧ d[i]? = some t ∧ w[i]? = some a ∧
        d[j]? = some t ∧ w[j]? = some b := by
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hab
    let i := (f 0).val; let j := (f 1).val
    have hij : i < j := f.strictMono (show (0 : Fin 2) < 1 by decide)
    have hi : (d.zip w)[i]? = some (t, a) := by
      rw [List.getElem?_eq_getElem (f 0).isLt]
      simpa using congrArg some (hf (0 : Fin 2)).symm
    have hj : (d.zip w)[j]? = some (t, b) := by
      rw [List.getElem?_eq_getElem (f 1).isLt]
      simpa using congrArg some (hf (1 : Fin 2)).symm
    obtain ⟨hdi, hwi⟩ := List.getElem?_zip_eq_some.mp hi
    obtain ⟨hdj, hwj⟩ := List.getElem?_zip_eq_some.mp hj
    exact ⟨i, j, hij, hdi, hwi, hdj, hwj⟩
  have mem_toggle_iff (s : Finset ℕ) (a b : ℕ) :
      a ∈ toggle s b ↔ if a = b then a ∉ s else a ∈ s := by
    by_cases hab : a = b
    · subst b
      by_cases ha : a ∈ s <;> simp [toggle_eq, ha]
    · by_cases hb : b ∈ s <;> simp [toggle_eq, hab, hb]
  have scan_first_second (a : ℕ) (w : List ℕ) (hw : w.count a = 2) :
      (scan ∅ w)[w.idxOf a]? = some U ∧
        (scan ∅ w)[NonnestingBasicOrders.secondPos a w]? = some D := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ :=
      NonnestingBasicOrders.count_two_decomposition a w hw
    have hf : (u ++ [a] ++ v ++ [a] ++ z).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hs : NonnestingBasicOrders.secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr; omega
      simp [NonnestingBasicOrders.secondPos, List.idxOf_append, hu, hv,
        List.drop_append, hdrop]
    constructor
    · rw [hf, scan_getElem?]
      simp [List.count_eq_zero.mpr hu, foldl_toggle_parity]
    · rw [hs, scan_getElem?]
      have hlen : (u ++ [a] ++ v).length = u.length + 1 + v.length := by
        simp; omega
      have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) := by
        simp [List.append_assoc]
      have ht : (u ++ [a] ++ v ++ [a] ++ z).take (u.length + 1 + v.length) =
          u ++ [a] ++ v := by
        rw [hword, ← hlen]; exact List.take_left
      have hget : (u ++ [a] ++ v ++ [a] ++ z)[u.length + 1 + v.length]? = some a := by
        rw [hword, ← hlen]; simp
      have hu0 : u.count a = 0 := List.count_eq_zero.mpr hu
      have hv0 : v.count a = 0 := List.count_eq_zero.mpr hv
      have hbefore : a ∉ u.foldl toggle ∅ := by
        have hpar := foldl_toggle_parity ∅ u a
        simpa [hu0] using hpar
      have hafter : a ∈ toggle (u.foldl toggle ∅) a := by
        simp [mem_toggle_iff, hbefore]
      rw [hget, Option.map_some, ht]; simp [foldl_toggle_parity, hv0, hafter]
  have scan_tag_position (t : DyckStep) (w : List ℕ) (a i : ℕ)
      (hc : w.count a = 2) (hwi : w[i]? = some a)
      (hti : (scan ∅ w)[i]? = some t) :
      i = if t = U then w.idxOf a
          else NonnestingBasicOrders.secondPos a w := by
    have hposition : i = w.idxOf a ∨
        i = NonnestingBasicOrders.secondPos a w := by
      obtain ⟨u, v, z, hu, hv, hz, rfl⟩ :=
        NonnestingBasicOrders.count_two_decomposition a w hc
      have hfirst : (u ++ [a] ++ v ++ [a] ++ z).idxOf a = u.length := by
        simp [List.idxOf_append, hu]
      have hsecond : NonnestingBasicOrders.secondPos a
          (u ++ [a] ++ v ++ [a] ++ z) = u.length + 1 + v.length := by
        have hdrop : u.drop (u.length + 1) = [] := by
          apply List.drop_eq_nil_iff.mpr; omega
        simp [NonnestingBasicOrders.secondPos, List.idxOf_append, hu, hv,
          List.drop_append, hdrop]
      rw [hfirst, hsecond]
      by_cases h0 : i < u.length
      · have hmem : a ∈ u := by
          have h : u[i]? = some a := by
            simpa [List.getElem?_append, h0] using hwi
          exact List.mem_of_getElem? h
        exact (hu hmem).elim
      by_cases h1 : i = u.length
      · exact Or.inl h1
      by_cases h2 : i < u.length + 1 + v.length
      · have hmem : a ∈ v := by
          have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
            simpa [List.getElem?_append, h0] using hwi
          have heq : i - u.length = (i - u.length - 1) + 1 := by omega
          rw [heq] at hi'
          have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
            simpa using hi'
          have hlt : i - u.length - 1 < v.length := by omega
          have hiv : v[i - u.length - 1]? = some a := by
            simpa [List.getElem?_append, hlt] using hi''
          exact List.mem_of_getElem? hiv
        exact (hv hmem).elim
      by_cases h3 : i = u.length + 1 + v.length
      · exact Or.inr h3
      · have hmem : a ∈ z := by
          have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
            simpa [List.getElem?_append, h0] using hwi
          have heq : i - u.length = (i - u.length - 1) + 1 := by omega
          rw [heq] at hi'
          have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
            simpa using hi'
          have hle : ¬ i - u.length - 1 < v.length := by omega
          have hi''' : (a :: z)[i - u.length - 1 - v.length]? = some a := by
            simpa [List.getElem?_append, hle] using hi''
          have heq' : i - u.length - 1 - v.length =
              (i - u.length - 1 - v.length - 1) + 1 := by omega
          rw [heq'] at hi'''
          have hiz : z[i - u.length - 1 - v.length - 1]? = some a := by
            simpa using hi'''
          exact List.mem_of_getElem? hiz
        exact (hz hmem).elim
    obtain ⟨hfirst, hsecond⟩ := scan_first_second a w hc
    rcases hposition with hi | hi
    · cases t with
      | U => simpa using hi
      | D => rw [hi, hfirst] at hti; cases hti
    · cases t with
      | U => rw [hi, hsecond] at hti; cases hti
      | D => simpa using hi
  have queue_pairwise_position (t : DyckStep) (w : List ℕ)
      (hw : ∀ a ∈ w, w.count a = 2) :
      (select t (scan ∅ w) w).Pairwise
        (fun a b =>
          (if t = U then w.idxOf a
           else NonnestingBasicOrders.secondPos a w) <
           (if t = U then w.idxOf b
           else NonnestingBasicOrders.secondPos b w)) := by
    apply List.pairwise_iff_forall_sublist.mpr; intro a b hab
    have hpair : List.Sublist [(t, a), (t, b)]
        ((select t (scan ∅ w) w).map (t, ·)) := by
      simpa using hab.map (t, ·)
    have htag : List.Sublist [(t, a), (t, b)] ((scan ∅ w).zip w) :=
      hpair.trans (tagged_select_sublist t (scan ∅ w) w)
    obtain ⟨i, j, hij, hti, hwi, htj, hwj⟩ :=
      tagged_pair_positions t (scan ∅ w) w a b htag
    have hca : w.count a = 2 := hw a (List.mem_of_getElem? hwi)
    have hcb : w.count b = 2 := hw b (List.mem_of_getElem? hwj)
    have hia := scan_tag_position t w a i hca hwi hti
    have hjb := scan_tag_position t w b j hcb hwj htj
    simpa [← hia, ← hjb] using hij
  have count_select_of_not_mem (t : DyckStep) (d : List DyckStep)
      (w : List ℕ) (a : ℕ) (ha : a ∉ w) :
      (select t d w).count a = 0 := by
    apply List.count_eq_zero.mpr; exact fun hm => ha ((select_sublist t d w).subset hm)
  have doubled_queue_count (w : List ℕ) (a : ℕ) (hw : w.count a = 2) :
      (select U (scan ∅ w) w).count a = 1 ∧
        (select D (scan ∅ w) w).count a = 1 := by
    obtain ⟨u, v, z, hu, hv, hz, rfl⟩ :=
      NonnestingBasicOrders.count_two_decomposition a w hw
    have hfold_u : a ∉ u.foldl toggle ∅ := by
      have h := foldl_toggle_parity ∅ u a
      simpa [List.count_eq_zero.mpr hu] using h
    have hfold_v : a ∈ v.foldl toggle (toggle (u.foldl toggle ∅) a) := by
      have h := foldl_toggle_parity (toggle (u.foldl toggle ∅) a) v a
      have ht : a ∈ toggle (u.foldl toggle ∅) a := by
        simp [mem_toggle_iff, hfold_u]
      simpa [List.count_eq_zero.mpr hv, ht] using h
    have hlen_u : (scan ∅ u).length = u.length := scan_length ∅ u
    have hlen_uav : (scan ∅ (u ++ [a] ++ v)).length =
        (u ++ [a] ++ v).length := scan_length ∅ (u ++ [a] ++ v)
    have hscan_first : scan (u.foldl toggle ∅) (a :: v) =
        U :: scan (toggle (u.foldl toggle ∅) a) v := by
      simp [scan, hfold_u]
    have hscan_second : scan (v.foldl toggle (toggle (u.foldl toggle ∅) a))
        (a :: z) = D :: scan
          (toggle (v.foldl toggle (toggle (u.foldl toggle ∅) a)) a) z := by
      simp [scan, hfold_v]
    have hfold_uav : (u ++ [a] ++ v).foldl toggle ∅ =
        v.foldl toggle (toggle (u.foldl toggle ∅) a) := by
      simp [List.foldl_append]
    have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) := by
      simp [List.append_assoc]
    have hscan_uav : scan ∅ (u ++ [a] ++ v) =
        scan ∅ u ++ U :: scan (toggle (u.foldl toggle ∅) a) v := by
      rw [show u ++ [a] ++ v = u ++ (a :: v) by simp [List.append_assoc],
        scan_append, hscan_first]
    rw [hword, scan_append, select_append U _ _ _ _ hlen_uav,
        select_append D _ _ _ _ hlen_uav]
    rw [hfold_uav, hscan_second]
    simp only [select, reduceCtorEq, ite_false, ite_true,
      List.count_append, List.count_cons, beq_self_eq_true]
    rw [hscan_uav,
        show u ++ [a] ++ v = u ++ (a :: v) by simp [List.append_assoc],
        select_append U _ _ _ _ hlen_u,
        select_append D _ _ _ _ hlen_u]
    simp [select, count_select_of_not_mem, hu, hv, hz]
  have nonnesting_of_equal_queues (w : List ℕ)
      (hw : ∀ a ∈ w, w.count a = 2)
      (heq : select U (scan ∅ w) w = select D (scan ∅ w) w) :
      ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w := by
    let p := select U (scan ∅ w) w
    have hU : p.Pairwise (fun a b =>
        w.idxOf a < w.idxOf b) := by
      simpa [p] using queue_pairwise_position U w hw
    have hD : p.Pairwise (fun a b =>
        NonnestingBasicOrders.secondPos a w < NonnestingBasicOrders.secondPos b w) := by
      simpa [p, heq] using queue_pairwise_position D w hw
    apply (NonnestingBasicOrders.nonnesting_iff_equal_orders w hw).mpr; intro a ha b hb hfirst
    have hca := hw a ha; have hcb := hw b hb
    have hpa : a ∈ p := by
      have hc := (doubled_queue_count w a hca).1; change p.count a = 1 at hc
      by_contra hn
      have hz := List.count_eq_zero.mpr hn; omega
    have hpb : b ∈ p := by
      have hc := (doubled_queue_count w b hcb).1; change p.count b = 1 at hc
      by_contra hn
      have hz := List.count_eq_zero.mpr hn; omega
    have hia : p.idxOf a < p.length := List.idxOf_lt_length_of_mem hpa
    have hib : p.idxOf b < p.length := List.idxOf_lt_length_of_mem hpb
    have hab : a ≠ b := by
      intro heq'; subst b; exact (Nat.lt_irrefl _ hfirst)
    have hidxne : p.idxOf a ≠ p.idxOf b := by
      intro heq'; exact hab ((List.idxOf_inj hpa).mp heq')
    have hidx : p.idxOf a < p.idxOf b := by
      by_contra hnot
      have hreverse : p.idxOf b < p.idxOf a := by omega
      have hrev := (List.pairwise_iff_getElem.mp hU) (p.idxOf b) (p.idxOf a)
        hib hia hreverse
      simp only [List.getElem_idxOf hib, List.getElem_idxOf hia] at hrev
      exact (Nat.lt_asymm hfirst hrev)
    have hresult := (List.pairwise_iff_getElem.mp hD) (p.idxOf a) (p.idxOf b)
      hia hib hidx
    simpa only [List.getElem_idxOf hia, List.getElem_idxOf hib] using hresult
  have encode_data (n : ℕ) (p : List ℕ)
      (hp : p.Perm (List.range' 1 n)) (d : DyckWord)
      (hlen : p.length = d.semilength) :
      let w := (weave p p d.toList).getD []
      ∃ hw : w.Perm ((List.range' 1 n).flatMap fun a => [a, a]),
        (¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
         ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) ∧
        shape (List.range' 1 n) w hw = d ∧
        select U (scan ∅ w) w = p := by
    dsimp; let w := (weave p p d.toList).getD []
    have hU : p.length = d.toList.count U := by
      simpa [DyckWord.semilength] using hlen
    obtain ⟨v, hv⟩ := weave_exists_of_counts p p d.toList hU
      (hU.trans d.count_U_eq_count_D)
    have hwv : weave p p d.toList = some w := by
      simp [w, hv]
    have hbase : w.Perm ((List.range' 1 n).flatMap fun a => [a, a]) :=
      (weave_perm p p d.toList w hwv).trans
        ((doubled_concat_perm p).trans (hp.flatMap_right fun a => [a, a]))
    have hsupport : ∀ a ∈ w, a ∈ List.range' 1 n := by
      intro a ha; have hb : a ∈ (List.range' 1 n).flatMap (fun b => [b, b]) := hbase.subset ha
      simpa using hb
    have hcount : ∀ a ∈ w, w.count a = 2 := by
      intro a ha; exact NonnestingBasicOrders.doubled_count n a w hbase (hsupport a ha)
    have hnodup : p.Nodup := (hp.nodup_iff).mpr List.nodup_range'
    have hscan : scan ∅ w = d.toList := scan_encode p d hnodup hlen
    have hselect := weave_select p p d.toList w hwv
    have hqueue : select U (scan ∅ w) w = select D (scan ∅ w) w := by
      simpa [hscan] using hselect.1.trans hselect.2.symm
    have hnn := nonnesting_of_equal_queues w hcount hqueue
    refine ⟨hbase, hnn, ?_, ?_⟩
    · apply DyckWord.ext
      exact hscan
    · change select U (scan ∅ w) w = p
      rw [hscan]; exact hselect.1
  have doubled_queues_perm (w : List ℕ)
      (hw : ∀ a ∈ w, w.count a = 2) :
      (select U (scan ∅ w) w).Perm (select D (scan ∅ w) w) := by
    apply List.perm_iff_count.mpr; intro a
    by_cases ha : a ∈ w
    · exact (doubled_queue_count w a (hw a ha)).1.trans
        (doubled_queue_count w a (hw a ha)).2.symm
    · rw [count_select_of_not_mem U _ w a ha,
        count_select_of_not_mem D _ w a ha]
  have equal_queues_of_nonnesting (w : List ℕ)
      (hw : ∀ a ∈ w, w.count a = 2)
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) :
      select U (scan ∅ w) w = select D (scan ∅ w) w := by
    let first := fun a (w : List ℕ) => w.idxOf a; let second := NonnestingBasicOrders.secondPos
    have horder := (NonnestingBasicOrders.nonnesting_iff_equal_orders w hw).mp hnn
    have hU : (select U (scan ∅ w) w).Pairwise
        (fun a b => first a w ≤ first b w) := by
      apply (queue_pairwise_position U w hw).imp; intro a b h
      exact Nat.le_of_lt (by simpa [first] using h)
    have hD : (select D (scan ∅ w) w).Pairwise
        (fun a b => first a w ≤ first b w) := by
      apply List.pairwise_iff_forall_sublist.mpr; intro a b hab
      have ha : a ∈ w := (select_sublist D (scan ∅ w) w).subset
        (hab.subset (by simp))
      have hb : b ∈ w := (select_sublist D (scan ∅ w) w).subset
        (hab.subset (by simp))
      have hsa : second a w < second b w := by
        simpa [second] using
          (queue_pairwise_position D w hw).forall_sublist hab
      have hca := hw a ha; have hcb := hw b hb
      have hne : first a w ≠ first b w := by
        intro heq; have hfa : w[first a w]? = some a := List.getElem?_idxOf ha
        have hfb : w[first b w]? = some b := List.getElem?_idxOf hb; rw [heq] at hfa
        have hab' : a = b := Option.some.inj (hfa.symm.trans hfb)
        subst b; exact (Nat.lt_irrefl _ hsa)
      by_contra hnot
      have hba : first b w < first a w := by omega
      have hsba : second b w < second a w := horder b hb a ha hba; exact (Nat.lt_asymm hsa hsba)
    apply (doubled_queues_perm w hw).eq_of_pairwise
      (le := fun a b => first a w ≤ first b w) _ hU hD
    intro a b ha hb hab hba; have ha' : a ∈ w := (select_sublist U (scan ∅ w) w).subset ha
    have hb' : b ∈ w := (select_sublist D (scan ∅ w) w).subset hb
    have hfa : w[first a w]? = some a := List.getElem?_idxOf ha'
    have hfb : w[first b w]? = some b := List.getElem?_idxOf hb'
    rw [Nat.le_antisymm hab hba] at hfa; exact Option.some.inj (hfa.symm.trans hfb)
  have decode_reconstruct (n : ℕ) (w : List ℕ)
      (hw : w.Perm ((List.range' 1 n).flatMap fun a => [a, a]))
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) :
      let p := select U (scan ∅ w) w; let d := shape (List.range' 1 n) w hw
      ∃ (_hp : p.Perm (List.range' 1 n))
        (hlen : p.length = d.semilength), (weave p p d.toList).getD [] = w := by
    dsimp; let p := select U (scan ∅ w) w; let d := shape (List.range' 1 n) w hw
    have hsupport : ∀ a ∈ w, a ∈ List.range' 1 n := by
      intro a ha; have hb : a ∈ (List.range' 1 n).flatMap (fun b => [b, b]) := hw.subset ha
      simpa using hb
    have hcount : ∀ a ∈ w, w.count a = 2 := by
      intro a ha; exact NonnestingBasicOrders.doubled_count n a w hw (hsupport a ha)
    have hp : p.Perm (List.range' 1 n) := by
      apply List.perm_iff_count.mpr; intro a
      by_cases ha : a ∈ List.range' 1 n
      · have hwa : a ∈ w := by
          apply hw.symm.subset; exact List.mem_flatMap.mpr ⟨a, ha, by simp⟩
        change (select U (scan ∅ w) w).count a = _; rw [(doubled_queue_count w a (hcount a hwa)).1]
        exact (List.count_eq_one_of_mem List.nodup_range' ha).symm
      · have hwa : a ∉ w := by
          intro hmem; exact ha (hsupport a hmem)
        change (select U (scan ∅ w) w).count a = _; rw [count_select_of_not_mem U _ w a hwa]
        exact (List.count_eq_zero.mpr ha).symm
    have hlen : p.length = d.semilength := by
      change (select U (scan ∅ w) w).length = (scan ∅ w).count U
      exact select_length U (scan ∅ w) w (scan_length ∅ w)
    have hqueue : select U (scan ∅ w) w = select D (scan ∅ w) w :=
      equal_queues_of_nonnesting w hcount hnn
    have hweave := weave_select_inverse (scan ∅ w) w (scan_length ∅ w); rw [← hqueue] at hweave
    refine ⟨hp, hlen, ?_⟩
    simp [shape, hweave]
  exact {
  toFun := fun x => by
    let p := x.val.1; let d := x.val.2; let hlen : p.length = d.semilength := x.property.2
    let w := (weave p p d.toList).getD []; let hdata := encode_data n p x.property.1 d hlen
    let hw := Classical.choose hdata; have hrest := Classical.choose_spec hdata
    exact ⟨w, by exact ⟨hw, hrest.1.1, hrest.1.2, by simp⟩⟩
  invFun := fun x => by
    let w := x.val; let hw := x.property.1; let p := select U (scan ∅ w) w
    let d := shape (List.range' 1 n) w hw
    let hdata := decode_reconstruct n w hw ⟨x.property.2.1, x.property.2.2.1⟩
    let hp := Classical.choose hdata; let hlen := Classical.choose (Classical.choose_spec hdata)
    exact ⟨(p, d), hp, hlen⟩
  left_inv := by
    rintro ⟨⟨p, d⟩, hp, hlen⟩
    obtain ⟨hw, hnn, hshape, hselect⟩ := encode_data n p hp d hlen
    apply Subtype.ext; apply Prod.ext
    · exact hselect
    · exact hshape
  right_inv := by
    rintro ⟨w, hw⟩
    obtain ⟨hp, hlen, hrec⟩ :=
      decode_reconstruct n w hw.1 ⟨hw.2.1, hw.2.2.1⟩
    apply Subtype.ext; exact hrec
  }
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBijection

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBijection.royalEncoding
