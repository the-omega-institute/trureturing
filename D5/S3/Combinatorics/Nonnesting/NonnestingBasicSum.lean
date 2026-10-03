/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicSum
   mirror-E: none(waiver:direct-sum-value-cuts)
   anchors: [mathlib/module/Mathlib.Data.List.Basic, mathlib/module/Mathlib.Data.Nat.Find]
   utility: none
   digest: Develops value cuts and localization of indecomposable patterns in sums. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

def shift (m : ℕ) (v : List ℕ) : List ℕ := v.map (fun x => x + m)

def directSum (m : ℕ) (u v : List ℕ) : List ℕ := u ++ shift m v

def valueCut (w : List ℕ) (k : ℕ) : Prop :=
  ∃ u v : List ℕ,
    w = u ++ v ∧ u.length = 2 * k ∧
      (∀ x ∈ u, 1 ≤ x ∧ x ≤ k) ∧ (∀ x ∈ v, k < x)

def primitive (w : List ℕ) (n : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k < n → ¬ valueCut w k

def sumIndecomposable (σ : List ℕ) : Prop :=
  ∀ k : Fin σ.length, 0 < k.val →
    ∃ i : Fin (σ.take k.val).length,
      ∃ j : Fin (σ.drop k.val).length,
        (σ.drop k.val).get j ≤ (σ.take k.val).get i

theorem directSum_perm (m n : ℕ) (u v : List ℕ)
    (hu : u.Perm ((List.range' 1 m).flatMap fun i => [i, i]))
    (hv : v.Perm ((List.range' 1 n).flatMap fun i => [i, i])) :
    (directSum m u v).Perm
      ((List.range' 1 (m + n)).flatMap fun i => [i, i]) := by
  have hshift : ∀ s k : ℕ,
      (((List.range' s k).flatMap fun i => [i, i]).map fun i => i + m) =
        ((List.range' (s + m) k).flatMap fun i => [i, i]) := by
    intro s k
    induction k generalizing s with
    | zero => simp
    | succ k ih =>
      simp [List.range'_succ, Nat.add_assoc, Nat.add_comm]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (s + 1)
  have hvshift : (shift m v).Perm
      ((List.range' (1 + m) n).flatMap fun i => [i, i]) := by
    simpa [shift, hshift] using hv.map (fun i => i + m)
  have h := hu.append hvshift
  rw [← List.flatMap_append, List.range'_append_1] at h
  exact h

theorem indecomposable_sublist_append (σ u v : List ℕ)
    (hσ : sumIndecomposable σ)
    (hsep : ∀ a ∈ u, ∀ b ∈ v, a < b)
    (hsub : List.Sublist σ (u ++ v)) :
    List.Sublist σ u ∨ List.Sublist σ v := by
  obtain ⟨p, q, hσpq, hpu, hqv⟩ := List.sublist_append_iff.mp hsub
  subst σ
  by_cases hp : p = []
  · subst p
    simpa using (Or.inr hqv :
      List.Sublist ([] ++ q) u ∨ List.Sublist ([] ++ q) v)
  by_cases hq : q = []
  · subst q
    left
    simpa using hpu
  have hk : p.length < (p ++ q).length := by
    simp only [List.length_append]
    have hqlen : 0 < q.length := List.length_pos_iff_ne_nil.mpr hq
    omega
  have hpge : 0 < p.length := List.length_pos_iff_ne_nil.mpr hp
  obtain ⟨i, j, hba⟩ := hσ ⟨p.length, hk⟩ hpge
  let a := ((p ++ q).take p.length).get i
  let b := ((p ++ q).drop p.length).get j
  have ha : a ∈ (p ++ q).take p.length := List.get_mem _ i
  have hb : b ∈ (p ++ q).drop p.length := List.get_mem _ j
  simp at ha hb
  have hau : a ∈ u := hpu.subset ha
  have hbv : b ∈ v := hqv.subset hb
  exfalso
  exact (Nat.not_lt_of_ge hba) (hsep a hau b hbv)

theorem indecomposable_map (σ : List ℕ) (x : ℕ → ℕ)
    (hσ : sumIndecomposable σ)
    (hpositive : ∀ a ∈ σ, 1 ≤ a)
    (hmono : ∀ i, 1 ≤ i → i < NonnestingDefs.letters σ → x i < x (i + 1)) :
    sumIndecomposable (σ.map x) := by
  have hboundAll : ∀ l : List ℕ, ∀ a ∈ l, a ≤ l.foldr max 0 := by
    intro l a ha
    induction l with
    | nil => simp at ha
    | cons c cs ih =>
      simp only [List.mem_cons] at ha
      simp only [List.foldr_cons]
      rcases ha with rfl | ha
      · exact Nat.le_max_left _ _
      · exact (ih ha).trans (Nat.le_max_right _ _)
  have hbound : ∀ a ∈ σ, a ≤ NonnestingDefs.letters σ := by
    intro a ha
    exact hboundAll σ a ha
  have hxmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ NonnestingDefs.letters σ →
      x i ≤ x j := by
    intro i j hi hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ j hj' ih =>
      exact (ih (by omega)).trans
        (Nat.le_of_lt (hmono j (by omega) (by omega)))
  intro k hkpos
  have hk' : k.val < σ.length := by simpa using k.isLt
  obtain ⟨i, j, hba⟩ := hσ ⟨k.val, hk'⟩ hkpos
  let a := (σ.take k.val).get i
  let b := (σ.drop k.val).get j
  have ha : a ∈ σ.take k.val := List.get_mem _ i
  have hb : b ∈ σ.drop k.val := List.get_mem _ j
  have haσ : a ∈ σ := List.mem_of_mem_take ha
  have hbσ : b ∈ σ := List.mem_of_mem_drop hb
  have hi : i.val < ((σ.map x).take k.val).length := by simpa using i.isLt
  have hj : j.val < ((σ.map x).drop k.val).length := by simpa using j.isLt
  refine ⟨⟨i.val, hi⟩, ⟨j.val, hj⟩, ?_⟩
  simpa [a, b] using hxmono b a (hpositive b hbσ) hba (hbound a haσ)

theorem occurs_directSum_iff (m : ℕ) (u v σ : List ℕ)
    (hu : ∀ a ∈ u, a ≤ m) (hv : ∀ b ∈ v, 1 ≤ b)
    (hσ : sumIndecomposable σ)
    (hpositive : ∀ a ∈ σ, 1 ≤ a)
    (hfull : ∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ) :
    NonnestingDefs.Occurs σ (directSum m u v) ↔
      NonnestingDefs.Occurs σ u ∨ NonnestingDefs.Occurs σ v := by
  unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
  constructor
  · rintro ⟨x, hxmono, _, hxsub, _⟩
    have hsep : ∀ a ∈ u, ∀ b ∈ shift m v, a < b := by
      intro a ha b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      have := hu a ha
      have := hv c hc
      omega
    have hloc := indecomposable_sublist_append (σ.map x) u (shift m v)
      (indecomposable_map σ x hσ hpositive hxmono) hsep hxsub
    rcases hloc with hleft | hright
    · left
      refine ⟨x, hxmono, ?_, hleft, by simp⟩
      intro i hi hile
      exact hleft.subset (List.mem_map_of_mem (hfull i hi hile))
    · right
      let y : ℕ → ℕ := fun i => x i - m
      have hxshift : ∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ →
          x i ∈ shift m v := by
        intro i hi hile
        exact hright.subset (List.mem_map_of_mem (hfull i hi hile))
      refine ⟨y, ?_, ?_, ?_, by simp⟩
      · intro i hi hilt
        have hxi := hxshift i hi (by omega)
        have hxi1 := hxshift (i + 1) (by omega) (by omega)
        obtain ⟨a, ha, hxa⟩ := List.mem_map.mp hxi
        obtain ⟨b, hb, hxb⟩ := List.mem_map.mp hxi1
        dsimp [y]
        have := hxmono i hi hilt
        omega
      · intro i hi hile
        obtain ⟨a, ha, hxa⟩ := List.mem_map.mp (hxshift i hi hile)
        have hy : y i = a := by dsimp [y]; omega
        exact hy ▸ ha
      · have hmapped := hright.map (fun a => a - m)
        simpa [y, shift, List.map_map, Function.comp_def] using hmapped
  · rintro (⟨x, hxmono, hxmem, hxsub, _⟩ | ⟨x, hxmono, hxmem, hxsub, _⟩)
    · refine ⟨x, hxmono, ?_, ?_, by simp⟩
      · intro i hi hile
        exact List.mem_append_left _ (hxmem i hi hile)
      · exact hxsub.trans (List.sublist_append_left u (shift m v))
    · let y : ℕ → ℕ := fun i => x i + m
      refine ⟨y, ?_, ?_, ?_, by simp⟩
      · intro i hi hilt
        dsimp [y]
        exact Nat.add_lt_add_right (hxmono i hi hilt) m
      · intro i hi hile
        apply List.mem_append_right u
        exact List.mem_map_of_mem (hxmem i hi hile)
      · have hmapped := hxsub.map (fun a => a + m)
        have hshift : List.Sublist (σ.map y) (shift m v) := by
          simpa [y, shift, List.map_map, Function.comp_def] using hmapped
        exact hshift.trans (List.sublist_append_right u (shift m v))

theorem valueCut_split_perm (n k : ℕ) (w : List ℕ)
    (hw : w.Perm ((List.range' 1 n).flatMap fun i => [i, i]))
    (hk : k ≤ n) (hcut : valueCut w k) :
    ∃ u v : List ℕ, w = directSum k u v ∧
      u.Perm ((List.range' 1 k).flatMap fun i => [i, i]) ∧
      v.Perm ((List.range' 1 (n - k)).flatMap fun i => [i, i]) := by
  obtain ⟨u, tail, heq, _, hu, htail⟩ := hcut
  have hrange : List.range' 1 n =
      List.range' 1 k ++ List.range' (k + 1) (n - k) := by
    have h := List.range'_append_1 (s := 1) (m := k) (n := n - k)
    simpa [Nat.add_sub_of_le hk, Nat.add_comm] using h.symm
  let low : List ℕ := (List.range' 1 k).flatMap fun i => [i, i]
  let high : List ℕ := (List.range' (k + 1) (n - k)).flatMap fun i => [i, i]
  have hbase : ((List.range' 1 n).flatMap fun i => [i, i]) = low ++ high := by
    simp [hrange, low, high, List.flatMap_append]
  have hlowRange : ∀ x ∈ low, x ≤ k := by
    intro x hx
    obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hx
    have hxi : x = i := by simpa using hii
    subst x
    have hir : 1 ≤ i ∧ i < 1 + k := by simpa using hi
    omega
  have hhighRange : ∀ x ∈ high, k < x := by
    intro x hx
    obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hx
    have hxi : x = i := by simpa using hii
    subst x
    have hir : k + 1 ≤ i ∧ i < k + 1 + (n - k) := by simpa using hi
    omega
  have huPerm : u.Perm low := by
    have hf := hw.filter (fun x => decide (x ≤ k))
    rw [heq, List.filter_append, hbase, List.filter_append] at hf
    have huFilter : u.filter (fun x => decide (x ≤ k)) = u := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [hu x hx |>.2]
    have htailFilter : tail.filter (fun x => decide (x ≤ k)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      simp [Nat.not_le.mpr (htail x hx)]
    have hlowFilter : low.filter (fun x => decide (x ≤ k)) = low := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [hlowRange x hx]
    have hhighFilter : high.filter (fun x => decide (x ≤ k)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      simp [Nat.not_le.mpr (hhighRange x hx)]
    simpa [huFilter, htailFilter, hlowFilter, hhighFilter] using hf
  have htailPerm : tail.Perm high := by
    have hf := hw.filter (fun x => decide (k < x))
    rw [heq, List.filter_append, hbase, List.filter_append] at hf
    have huFilter : u.filter (fun x => decide (k < x)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      simp [Nat.not_lt.mpr (hu x hx |>.2)]
    have htailFilter : tail.filter (fun x => decide (k < x)) = tail := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [htail x hx]
    have hlowFilter : low.filter (fun x => decide (k < x)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      simp [Nat.not_lt.mpr (hlowRange x hx)]
    have hhighFilter : high.filter (fun x => decide (k < x)) = high := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [hhighRange x hx]
    simpa [huFilter, htailFilter, hlowFilter, hhighFilter] using hf
  let v := tail.map (fun x => x - k)
  have hrestore : shift k v = tail := by
    unfold shift v
    rw [List.map_map]
    calc
      tail.map ((fun x => x + k) ∘ (fun x => x - k)) = tail.map id := by
        apply List.map_congr_left
        intro x hx
        simp only [Function.comp_apply, id_eq]
        have := htail x hx
        omega
      _ = tail := List.map_id tail
  have hshiftBase : shift k ((List.range' 1 (n - k)).flatMap fun i => [i, i]) =
      high := by
    have hmap : ∀ s j : ℕ,
        (((List.range' s j).flatMap fun i => [i, i]).map fun i => i + k) =
          ((List.range' (s + k) j).flatMap fun i => [i, i]) := by
      intro s j
      induction j generalizing s with
      | zero => simp
      | succ j ih =>
        simp [List.range'_succ, Nat.add_assoc, Nat.add_comm]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (s + 1)
    simpa [shift, high, Nat.add_comm] using hmap 1 (n - k)
  have hvPerm : v.Perm ((List.range' 1 (n - k)).flatMap fun i => [i, i]) := by
    have h := htailPerm.map (fun x => x - k)
    rw [← hshiftBase] at h
    have hcancel : ∀ l : List ℕ, (shift k l).map (fun x => x - k) = l := by
      intro l
      unfold shift
      rw [List.map_map]
      calc
        l.map ((fun x => x - k) ∘ (fun x => x + k)) = l.map id := by
          apply List.map_congr_left
          intro x hx
          simp
        _ = l := List.map_id l
    simpa [v, hcancel] using h
  exact ⟨u, v, by simpa [directSum, hrestore] using heq, by simpa [low] using huPerm,
    hvPerm⟩

theorem first_primitive_factor (n : ℕ) (w : List ℕ)
    (hw : w.Perm ((List.range' 1 n).flatMap fun i => [i, i]))
    (hn : 0 < n) :
    ∃ k u v, 1 ≤ k ∧ k ≤ n ∧ w = directSum k u v ∧ primitive u k ∧
      u.Perm ((List.range' 1 k).flatMap fun i => [i, i]) ∧
      v.Perm ((List.range' 1 (n - k)).flatMap fun i => [i, i]) := by
  classical
  let p : ℕ → Prop := fun k => k = n ∨ (1 ≤ k ∧ valueCut w k)
  have hex : ∃ k, p k := ⟨n, Or.inl rfl⟩
  let k := Nat.find hex
  have hkp : p k := Nat.find_spec hex
  have hkle : k ≤ n := Nat.find_min' hex (Or.inl rfl)
  have hkpos : 1 ≤ k := by
    rcases hkp with hkn | ⟨hk, _⟩
    · omega
    · exact hk
  by_cases hkn : k = n
  · have hprimitive : primitive w k := by
      intro j hj hjn hjcut
      have hpj : p j := Or.inr ⟨hj, hjcut⟩
      have hmin : k ≤ j := Nat.find_min' hex hpj
      omega
    refine ⟨k, w, [], hkpos, hkle, ?_, hprimitive, ?_, ?_⟩
    · simp [directSum, shift]
    · simpa [hkn] using hw
    · simp [hkn]
  · have hcut : valueCut w k := (hkp.resolve_left hkn).2
    obtain ⟨u, v, heq, huperm, hvperm⟩ := valueCut_split_perm n k w hw hkle hcut
    have hvpositive : ∀ x ∈ v, 1 ≤ x := by
      intro x hx
      have hbase := hvperm.mem_iff.mp hx
      obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hbase
      have hxi : x = i := by simpa using hii
      subst x
      have hirange : 1 ≤ i ∧ i < 1 + (n - k) := by simpa using hi
      exact hirange.1
    have hprimitive : primitive u k := by
      intro j hj hjk hjcut
      obtain ⟨a, b, hab, halen, ha, hb⟩ := hjcut
      have hcutw : valueCut w j := by
        refine ⟨a, b ++ shift k v, ?_, halen, ha, ?_⟩
        · rw [heq, hab]
          simp [directSum, List.append_assoc]
        · intro x hx
          rcases List.mem_append.mp hx with hxb | hxv
          · exact hb x hxb
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxv
            have := hvpositive y hy
            omega
      have hpj : p j := Or.inr ⟨hj, hcutw⟩
      have hmin : k ≤ j := Nat.find_min' hex hpj
      omega
    exact ⟨k, u, v, hkpos, hkle, heq, hprimitive, huperm, hvperm⟩

theorem primitive_split_unique (w u v u' v' : List ℕ) (k j : ℕ)
    (hw : w = directSum k u v) (hw' : w = directSum j u' v')
    (hlen : u.length = 2 * k) (hlen' : u'.length = 2 * j)
    (hubound : ∀ x ∈ u, 1 ≤ x ∧ x ≤ k)
    (hubound' : ∀ x ∈ u', 1 ≤ x ∧ x ≤ j)
    (hvpositive : ∀ x ∈ v, 1 ≤ x)
    (hvpositive' : ∀ x ∈ v', 1 ≤ x)
    (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hprimitive : primitive u k) (hprimitive' : primitive u' j) :
    k = j ∧ u = u' ∧ v = v' := by
  have cutPrefix (p q : List ℕ) (i : ℕ)
      (hcut : valueCut (p ++ q) i) (hle : 2 * i ≤ p.length) :
      valueCut p i := by
    obtain ⟨a, b, heq, halen, ha, hb⟩ := hcut
    have htake : p.take (2 * i) = a := by
      calc
        p.take (2 * i) = (p ++ q).take (2 * i) := by
          rw [List.take_append_of_le_length hle]
        _ = a := by rw [heq]; simp [halen]
    have hdrop : (p ++ q).drop (2 * i) = b := by
      rw [heq]
      simp [halen]
    refine ⟨p.take (2 * i), p.drop (2 * i), (List.take_append_drop (2 * i) p).symm,
      ?_, ?_, ?_⟩
    · simp [hle]
    · simpa [htake] using ha
    · intro x hx
      have hx' : x ∈ (p ++ q).drop (2 * i) := by
        rw [List.drop_append_of_le_length hle]
        exact List.mem_append_left _ hx
      exact hb x (hdrop ▸ hx')
  have hkj : k ≤ j := by
    by_contra hnot
    have hjk : j < k := by omega
    have hcut : valueCut w j := by
      rw [hw']
      refine ⟨u', shift j v', rfl, hlen', hubound', ?_⟩
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hvpositive' y hy
      omega
    rw [hw] at hcut
    have hinside : valueCut u j :=
      cutPrefix u (shift k v) j hcut (by omega)
    exact hprimitive j hj hjk hinside
  have hjk : j ≤ k := by
    by_contra hnot
    have hkj' : k < j := by omega
    have hcut : valueCut w k := by
      rw [hw]
      refine ⟨u, shift k v, rfl, hlen, hubound, ?_⟩
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hvpositive y hy
      omega
    rw [hw'] at hcut
    have hinside : valueCut u' k :=
      cutPrefix u' (shift j v') k hcut (by omega)
    exact hprimitive' k hk hkj' hinside
  have hkeq : k = j := by omega
  subst j
  have hU : u = u' := by
    have huTake : w.take (2 * k) = u := by
      rw [hw]
      simpa [directSum, hlen] using
        (List.take_append_of_le_length (Nat.le_refl u.length) (l₂ := shift k v))
    have huTake' : w.take (2 * k) = u' := by
      rw [hw']
      simpa [directSum, hlen'] using
        (List.take_append_of_le_length (Nat.le_refl u'.length) (l₂ := shift k v'))
    exact huTake.symm.trans huTake'
  have hV : v = v' := by
    have heq : shift k v = shift k v' := by
      apply List.append_cancel_left
      calc
        u ++ shift k v = w := hw.symm
        _ = u' ++ shift k v' := hw'
        _ = u ++ shift k v' := by rw [hU]
    exact (List.map_inj_right (fun x y h => by omega)).mp heq
  exact ⟨rfl, hU, hV⟩

end D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum.first_primitive_factor
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum.primitive_split_unique
