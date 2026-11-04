/- GID: D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal ascending daughter blocks with one shortened top block. -/
import D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening.Arithmetic

/-! Ascending physical block inventories and the literal common-cut ear. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators

theorem length_split (d r : ℕ) (hr : 2 ≤ r) :
    length d r = (r - 1) * (d + 1) + d := by
  have he : (d + 1) * r = (r - 1) * (d + 1) + (d + 1) := by
    calc
      _ = (d + 1) * ((r - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
      _ = _ := by ring
  dsimp [length]; omega

/-- Every low local ear is an ordinary OLD label. -/
def regularLabel (d r : ℕ) (hr : 2 ≤ r) (j : Fin (r - 1))
    (i : Fin (d + 1)) : Fin (length d r) :=
  ⟨j.val * (d + 1) + i.val, by
    rw [length_split d r hr]
    have hh := Nat.mul_le_mul_right (d + 1) (show j.val + 1 ≤ r - 1 by omega)
    nlinarith [i.isLt]⟩

def topLabel (d r : ℕ) (hr : 2 ≤ r) (i : Fin d) : Fin (length d r) :=
  ⟨(r - 1) * (d + 1) + i.val, by rw [length_split d r hr]; omega⟩

def daughterLabel (d r : ℕ) (hr : 2 ≤ r) (j : Fin r)
    (i : Fin (d + 1)) : Fin (length d r + 1) :=
  ⟨j.val * (d + 1) + i.val, by
    have he : length d r + 1 = (d + 1) * r := by
      have := Nat.mul_pos (show 0 < d + 1 by omega) (show 0 < r by omega)
      dsimp [length]; omega
    rw [he]
    have hh := Nat.mul_le_mul_right (d + 1) (show j.val + 1 ≤ r by omega)
    nlinarith [i.isLt]⟩

def lowerWord (d r : ℕ) (hr : 2 ≤ r) (eta : List (Fin (d + 1))) :
    List (Fin (length d r)) :=
  (List.finRange (r - 1)).flatMap (fun j => eta.map (regularLabel d r hr j))

def shortenedWord (d r : ℕ) (hr : 2 ≤ r) (tau : List (Fin d)) (cut : ℕ) :
    List (Fin (length d r)) :=
  lowerWord d r hr (earWord d tau cut) ++ tau.map (topLabel d r hr)

def commonCut (d r cut : ℕ) : ℕ := (r - 1) * (d + 1) + cut

def daughterWord (d r : ℕ) (hr : 2 ≤ r) (eta : List (Fin (d + 1))) :
    List (Fin (length d r + 1)) :=
  (List.finRange r).flatMap (fun j => eta.map (daughterLabel d r hr j))

/-- Port of the consumed private ear-prefix lemma from RunFirstEarTransport
at 447f4235385fe941888b620340cd4429dfbf0e61. It includes saturated takes. -/
theorem ear_prefix_sum (d : ℕ) (sigma : List (Fin d)) (cut : ℕ)
    (hc : cut ≤ sigma.length) (f : Fin (d + 1) → ℤ) (h : ℕ) :
    (((earWord d sigma cut).take h).map f).sum =
      ((sigma.take (if h ≤ cut then h else h - 1)).map
        (fun i => f i.castSucc)).sum + (if h ≤ cut then 0 else f (Fin.last d)) := by
  induction sigma generalizing cut h with
  | nil =>
      have : cut = 0 := by simpa using hc
      subst cut
      cases h <;> simp [earWord]
  | cons x xs ih =>
      cases cut with
      | zero =>
          cases h with
          | zero => simp [earWord]
          | succ h => simp [earWord, List.map_map, Function.comp_def, add_comm]
      | succ cut =>
          have hc' : cut ≤ xs.length := by simpa using hc
          cases h with
          | zero => simp [earWord]
          | succ h =>
              have he := ih cut hc' h
              simp only [earWord, List.take_succ_cons, List.drop_succ_cons,
                List.map_cons, List.cons_append, List.sum_cons] at he ⊢
              split_ifs with hh
              · have hh' : h ≤ cut := by omega
                simpa [hh', List.take_succ_cons, List.sum_cons, add_assoc] using
                  congrArg (f x.castSucc + ·) he
              · have hh' : ¬ h ≤ cut := by omega
                simpa [hh', show h + 1 - 1 = (h - 1) + 1 by omega,
                  List.take_succ_cons, List.sum_cons, add_assoc] using
                  congrArg (f x.castSucc + ·) he

theorem ear_sum (d : ℕ) (tau : List (Fin d)) (cut : ℕ) (f : Fin (d + 1) → ℤ) :
    ((earWord d tau cut).map f).sum =
      (tau.map (fun i => f i.castSucc)).sum + f (Fin.last d) := by
  have he := congrArg (fun xs : List (Fin d) =>
    (xs.map (fun i => f i.castSucc)).sum) (List.take_append_drop cut tau)
  simp only [List.map_append, List.sum_append] at he
  simp only [earWord, List.map_append, List.map_map, Function.comp_def,
    List.sum_append, List.map_singleton, List.sum_singleton]
  omega

theorem lower_length (d r cut : ℕ) (hr : 2 ≤ r) (tau : List (Fin d))
    (htau : tau.Perm (List.finRange d)) :
    (lowerWord d r hr (earWord d tau cut)).length = (r - 1) * (d + 1) := by
  have ht : tau.length = d := by simpa using htau.length_eq
  have he : (earWord d tau cut).length = d + 1 := by
    simp only [earWord, List.length_append, List.length_map, List.length_singleton]
    have hh := congrArg List.length (List.take_append_drop cut tau)
    simp only [List.length_append] at hh
    omega
  unfold lowerWord
  have hlen (s : List (Fin (r - 1))) :
      (s.flatMap (fun j => (earWord d tau cut).map (regularLabel d r hr j))).length =
        s.length * (d + 1) := by
    induction s with
    | nil => simp
    | cons x xs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map,
          List.length_cons, ih, he]
        ring
  simpa using hlen (List.finRange (r - 1))

theorem ear_after (k : ℕ) (xs ys : List (Fin k)) (cut : ℕ) :
    earWord k (xs ++ ys) (xs.length + cut) =
      xs.map Fin.castSucc ++ earWord k ys cut := by
  induction xs with
  | nil => simp [earWord]
  | cons x xs ih =>
      simpa only [List.length_cons, Nat.succ_add, List.cons_append, earWord,
        List.take_succ_cons, List.drop_succ_cons, List.map_cons] using
          congrArg (fun zs => x.castSucc :: zs) ih

theorem literal_ear (d r cut : ℕ) (hr : 2 ≤ r) (tau : List (Fin d))
    (htau : tau.Perm (List.finRange d)) :
    earWord (length d r) (shortenedWord d r hr tau cut) (commonCut d r cut) =
      daughterWord d r hr (earWord d tau cut) := by
  have hl := lower_length d r cut hr tau htau
  have hlow (j : Fin (r - 1)) (i : Fin (d + 1)) :
      (regularLabel d r hr j i).castSucc =
        daughterLabel d r hr ⟨j.val, by omega⟩ i := Fin.ext rfl
  let jt : Fin r := ⟨r - 1, by omega⟩
  have htop (i : Fin d) : (topLabel d r hr i).castSucc =
      daughterLabel d r hr jt i.castSucc := Fin.ext rfl
  have hfresh : Fin.last (length d r) = daughterLabel d r hr jt (Fin.last d) := by
    apply Fin.ext
    simpa [daughterLabel, jt] using length_split d r hr
  have hte : earWord (length d r) (tau.map (topLabel d r hr)) cut =
      (earWord d tau cut).map (daughterLabel d r hr jt) := by
    simp only [earWord, ← List.map_take, ← List.map_drop, List.map_append,
      List.map_map, List.map_singleton, Function.comp_def]
    simp_rw [htop]
    rw [hfresh]
  have hfr : List.finRange r =
      (List.finRange (r - 1)).map (fun j => (⟨j.val, by omega⟩ : Fin r)) ++ [jt] := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    have hh : List.finRange (s + 1) =
        (List.finRange s).map Fin.castSucc ++ [Fin.last s] :=
      List.finRange_succ_last
    have hh' : List.finRange (s + 1) =
        (List.finRange s).map (fun j =>
          (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (s + 1))) ++
            [⟨s, Nat.lt_succ_self s⟩] := by
      rw [hh]
      apply congrArg₂ List.append
      · apply List.map_congr_left
        intro j _
        exact Fin.ext rfl
      · apply congrArg List.singleton
        exact Fin.ext rfl
    simpa only [jt, Nat.succ_sub_one, Nat.add_sub_cancel] using hh'
  unfold shortenedWord commonCut
  rw [← hl, ear_after, hte]
  unfold daughterWord
  rw [hfr]
  simp only [List.flatMap_append, List.flatMap_map, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  congr 1
  simp only [lowerWord, List.map_flatMap, List.map_map, Function.comp_def]
  apply congrArg (fun f : Fin (r - 1) → List (Fin (length d r + 1)) =>
    (List.finRange (r - 1)).flatMap f)
  funext j
  apply List.map_congr_left
  intro i hi
  exact hlow j i

/-- The product-inventory proof is the ascending version of the consumed
private block_perm argument in PhysicalJointRepetition at settled
51518b6ee6ccebd7ee3cb0e03e5c13589a570a9c. No transport theorem is imported. -/
theorem daughter_perm (d r : ℕ) (hr : 2 ≤ r) (eta : List (Fin (d + 1)))
    (heta : eta.Perm (List.finRange (d + 1))) :
    (daughterWord d r hr eta).Perm (List.finRange (length d r + 1)) := by
  classical
  let θ : Fin r × Fin (d + 1) → Fin (length d r + 1) :=
    fun p => daughterLabel d r hr p.1 p.2
  have hinj : Function.Injective θ := by
    rintro ⟨j, i⟩ ⟨k, h⟩ he
    have hv := congrArg Fin.val he
    change j.val * (d + 1) + i.val = k.val * (d + 1) + h.val at hv
    have hjk : j.val = k.val := by
      have hjd : (j.val * (d + 1) + i.val) / (d + 1) = j.val := by
        apply Nat.div_eq_of_lt_le
        · omega
        · nlinarith [i.isLt]
      have hkd : (k.val * (d + 1) + h.val) / (d + 1) = k.val := by
        apply Nat.div_eq_of_lt_le
        · omega
        · nlinarith [h.isLt]
      have hh := congrArg (fun z => z / (d + 1)) hv
      rw [hjd, hkd] at hh
      exact hh
    rw [hjk] at hv
    have hih : i.val = h.val := by omega
    exact Prod.ext (Fin.ext hjk) (Fin.ext hih)
  let row : Fin r → List (Fin (length d r + 1)) :=
    fun j => (List.finRange (d + 1)).map (fun i => θ (j, i))
  have hcomplete : ((List.finRange r).flatMap row).Perm
      (List.finRange (length d r + 1)) := by
    have he : (List.finRange r).flatMap row =
        ((List.finRange r).product (List.finRange (d + 1))).map θ := by
      simp only [row, List.product, List.map_flatMap, List.map_map, Function.comp_def]
    rw [he]
    apply (List.perm_ext_iff_of_nodup
      (((List.nodup_finRange r).product (List.nodup_finRange (d + 1))).map hinj)
      (List.nodup_finRange _)).mpr
    intro x
    simp only [List.mem_finRange, iff_true]
    have hlen : length d r + 1 = (d + 1) * r := by
      have := Nat.mul_pos (show 0 < d + 1 by omega) (show 0 < r by omega)
      dsimp [length]; omega
    let j : Fin r := ⟨x.val / (d + 1), by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).2
      have hx : x.val < (d + 1) * r := by rw [← hlen]; exact x.isLt
      simpa only [Nat.mul_comm] using hx⟩
    let i : Fin (d + 1) := ⟨x.val % (d + 1), Nat.mod_lt _ (by omega)⟩
    have hv : θ (j, i) = x := by
      apply Fin.ext
      simpa [θ, daughterLabel, j, i, Nat.add_comm, Nat.mul_comm] using
        Nat.mod_add_div x.val (d + 1)
    exact List.mem_map.mpr ⟨(j, i), by simp, hv⟩
  exact (List.Perm.flatMap_left _ (fun j _ => heta.map _)).trans hcomplete

theorem ear_perm (d : ℕ) (tau : List (Fin d)) (cut : ℕ)
    (htau : tau.Perm (List.finRange d)) :
    (earWord d tau cut).Perm (List.finRange (d + 1)) := by
  have he : (earWord d tau cut).Perm (tau.map Fin.castSucc ++ [Fin.last d]) := by
    unfold earWord
    rw [List.map_take, List.map_drop]
    have hp := (List.perm_append_comm :
      ([Fin.last d] ++ (tau.map Fin.castSucc).drop cut).Perm
        ((tau.map Fin.castSucc).drop cut ++ [Fin.last d])).append_left
          ((tau.map Fin.castSucc).take cut)
    have hj : (tau.map Fin.castSucc).take cut ++
        ((tau.map Fin.castSucc).drop cut ++ [Fin.last d]) =
        tau.map Fin.castSucc ++ [Fin.last d] := by
      rw [← List.append_assoc, List.take_append_drop]
    rw [hj] at hp
    simpa only [List.append_assoc] using hp
  exact he.trans (by simpa [List.finRange_succ_last] using
    (htau.map Fin.castSucc).append_right [Fin.last d])

/-- Delete just the globally fresh label; all local ear labels survive. -/
def removeFresh (k : ℕ) (i : Fin (k + 1)) : Option (Fin k) :=
  if hi : i.val < k then some ⟨i.val, hi⟩ else none

theorem old_perm_of_ear (k : ℕ) (sigma : List (Fin k)) (cut : ℕ)
    (he : (earWord k sigma cut).Perm (List.finRange (k + 1))) :
    sigma.Perm (List.finRange k) := by
  have hmap (xs : List (Fin k)) :
      (xs.map Fin.castSucc).filterMap (removeFresh k) = xs := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [removeFresh, x.isLt, ih]
  have hf : removeFresh k (Fin.last k) = none := by simp [removeFresh]
  have hleft : (earWord k sigma cut).filterMap (removeFresh k) = sigma := by
    simp only [earWord, List.filterMap_append, List.filterMap_cons, hf,
      List.filterMap_nil, hmap, List.append_nil]
    exact List.take_append_drop cut sigma
  have hright : (List.finRange (k + 1)).filterMap (removeFresh k) = List.finRange k := by
    rw [List.finRange_succ_last, List.filterMap_append, hmap]
    simp [hf]
  have hh := he.filterMap (removeFresh k)
  simpa only [hleft, hright] using hh

theorem shortened_perm (d r cut : ℕ) (hr : 2 ≤ r) (tau : List (Fin d))
    (htau : tau.Perm (List.finRange d)) :
    (shortenedWord d r hr tau cut).Perm (List.finRange (length d r)) := by
  apply old_perm_of_ear (length d r) _ (commonCut d r cut)
  rw [literal_ear d r cut hr tau htau]
  exact daughter_perm d r hr _ (ear_perm d tau cut htau)

end D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening
