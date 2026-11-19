/- GID: D5/S3/Combinatorics/Golomb/EqualityReplay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Golomb/EqualityReplay
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikMinimizers.result; instance=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8
   digest: Checked equality leaves prove integral gaps and normalized marks. -/

import D5.S3.Combinatorics.Golomb.Replay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Golomb.Replay

open scoped BigOperators

def affineCombination {n : ℕ} (get : Ref → Option (Row n)) (support : Weights) :
    List (ℕ × ℤ) → Option (Row n)
  | [] => some (.zero n)
  | (index, c) :: rest => do
    let (ref, w) ← support[index]?
    if w ≤ 0 then none else
      let r ← get ref
      let tail ← affineCombination get support rest
      pure (r.addScaled c tail)

private theorem affine_combination_eq {n : ℕ} {get : Ref → Option (Row n)} {support : Weights}
    {coefficients : List (ℕ × ℤ)} {total : Row n} {g : Fin n → ℝ}
    (ht : supportTight get support g)
    (hc : affineCombination get support coefficients = some total) :
    eval total.normal g = (total.rhs : ℝ) := by
  induction coefficients generalizing total with
  | nil =>
    have he : Row.zero n = total := Option.some.inj hc
    subst total
    simp [Row.zero, eval]
  | cons item rest ih =>
    obtain ⟨index, c⟩ := item
    cases hw : support[index]? with
    | none => simp [affineCombination, hw] at hc
    | some pair =>
      obtain ⟨ref, w⟩ := pair
      by_cases hpos : 0 < w
      · have hn := not_le_of_gt hpos
        cases hr : get ref with
        | none => simp [affineCombination, hw, hr, hn] at hc
        | some r =>
          cases hs : affineCombination get support rest with
          | none => simp [affineCombination, hw, hr, hs, hn] at hc
          | some s =>
            have he : r.addScaled c s = total := by
              simpa [affineCombination, hw, hr, hs, hn] using hc
            subst total
            change eval (fun i => c * r.normal i + s.normal i) g =
              ((c * r.rhs + s.rhs : ℤ) : ℝ)
            rw [eval_add, eval_scale, Int.cast_add, Int.cast_mul, ih hs,
              ht ref w (List.mem_of_getElem? hw) hpos r hr]
      · simp [affineCombination, hw, le_of_not_gt hpos] at hc

def IsIntegral (x : ℝ) : Prop := ∃ z : ℤ, x = (z : ℝ)

def IntegralGaps {n : ℕ} (g : Fin n → ℝ) : Prop := ∀ i, IsIntegral (g i)

private theorem IsIntegral.add {x y : ℝ} (hx : IsIntegral x) (hy : IsIntegral y) :
    IsIntegral (x + y) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact ⟨u + v, by push_cast; rfl⟩

private theorem IsIntegral.zsmul {x : ℝ} (hx : IsIntegral x) (c : ℤ) :
    IsIntegral ((c : ℝ) * x) := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨c * u, by push_cast; rfl⟩

def tightRow {n : ℕ} (get : Ref → Option (Row n)) (support : Weights) (index : ℕ) :
    Option (Row n) := do
  let (ref, w) ← support[index]?
  if 0 < w then get ref else none

private theorem tightRow_eq {n : ℕ} {get : Ref → Option (Row n)} {support : Weights}
    {g : Fin n → ℝ} (ht : supportTight get support g) {i : ℕ} {r : Row n}
    (h : tightRow get support i = some r) : eval r.normal g = (r.rhs : ℝ) := by
  cases hs : support[i]? with
  | none => simp [tightRow, hs] at h
  | some entry =>
    obtain ⟨ref, w⟩ := entry
    by_cases hw : 0 < w
    · exact ht ref w (List.mem_of_getElem? hs) hw r (by simpa [tightRow, hs, hw] using h)
    · simp [tightRow, hs, hw] at h

def tightPack {n : ℕ} (data : Array (Static n)) (support : Weights) (index : ℕ) :
    Option (List (Span n)) := do
  let (ref, w) ← support[index]?
  if 0 < w then
    match ref with
    | .static i =>
      match data[i]? with
      | some (.pack slots b) =>
        if slots.Nodup ∧ 2 * b = (slots.length : ℤ) * (slots.length + 1) then
          some slots
        else none
      | _ => none
    | .branch _ => none
  else none

private theorem tightPack_ranks {n : ℕ} {data : Array (Static n)} {support : Weights}
    {path : List (Row n)} {g : Fin n → ℝ}
    (ht : supportTight (lookup (staticRows data) path) support g) (hg : Separated g)
    {i : ℕ} {slots : List (Span n)} (h : tightPack data support i = some slots) :
    ∃ p : Equiv.Perm (Fin slots.length),
      ∀ j, eval (slots.get j).normal g = ((p j).val : ℝ) + 1 := by
  cases hs : support[i]? with
  | none => simp [tightPack, hs] at h
  | some entry =>
    obtain ⟨ref, w⟩ := entry
    by_cases hw : 0 < w
    · cases ref with
      | branch k => simp [tightPack, hs, hw] at h
      | static k =>
        cases hd : data[k]? with
        | none => simp [tightPack, hs, hw, hd] at h
        | some s =>
          cases s with
          | mirror => simp [tightPack, hs, hw, hd] at h
          | unit j => simp [tightPack, hs, hw, hd] at h
          | sub q b => simp [tightPack, hs, hw, hd] at h
          | pack qs b =>
            by_cases hp : qs.Nodup ∧ 2 * b = (qs.length : ℤ) * (qs.length + 1)
            · have he : qs = slots := by simpa [tightPack, hs, hw, hd, hp] using h
              subst slots
              have hget : lookup (staticRows data) path (.static k) =
                  some (Static.pack qs b).row := by simp [lookup, staticRows, hd]
              have heq := ht (.static k) w (List.mem_of_getElem? hs) hw _ hget
              change eval (Span.normalSum (fun j : Fin qs.length => qs.get j)) g =
                (b : ℝ) at heq
              rw [eval_normalSum] at heq
              have htri : (2 : ℝ) * (b : ℝ) =
                  (qs.length : ℝ) * ((qs.length : ℝ) + 1) := by exact_mod_cast hp.2
              exact packing_slots_of_saturation
                (fun j => eval (qs.get j).normal g) (fun j => span_min (qs.get j) hg)
                (fun j k hjk => span_separation hg
                  (fun he => hjk (List.nodup_iff_injective_get.mp hp.1 he)))
                (by rw [heq]; linarith)
            · simp [tightPack, hs, hw, hd, hp] at h
    · simp [tightPack, hs, hw] at h

def rankedSlot {n : ℕ} (data : Array (Static n)) (support : Weights) (i j : ℕ) :
    Option (Span n × ℕ) := do
  let slots ← tightPack data support i
  let q ← slots[j]?
  pure (q, slots.length)

private theorem rankedSlot_rank {n : ℕ} {data : Array (Static n)} {support : Weights}
    {path : List (Row n)} {g : Fin n → ℝ}
    (ht : supportTight (lookup (staticRows data) path) support g) (hg : Separated g)
    {i j m : ℕ} {q : Span n} (h : rankedSlot data support i j = some (q, m)) :
    ∃ k : Fin m, eval q.normal g = (k.val : ℝ) + 1 := by
  cases hp : tightPack data support i with
  | none => simp [rankedSlot, hp] at h
  | some slots =>
    by_cases hj : j < slots.length
    · have he : (slots[j], slots.length) = (q, m) := by
        simpa [rankedSlot, hp, List.getElem?_eq_getElem hj] using h
      have hq : slots.get ⟨j, hj⟩ = q := (Prod.mk.inj he).1
      have hm := (Prod.mk.inj he).2
      subst m
      obtain ⟨p, hr⟩ := tightPack_ranks ht hg hp
      exact ⟨p ⟨j, hj⟩, hq ▸ hr ⟨j, hj⟩⟩
    · simp [rankedSlot, hp, List.getElem?_eq_none (Nat.le_of_not_gt hj)] at h

inductive LeafRowRef where
  | original (ref : Ref)
  | tight (index : ℕ) (negative : Bool)
  | extra (index : ℕ)

def negRow {n : ℕ} (r : Row n) : Row n :=
  ⟨fun i => -r.normal i, -r.rhs⟩

def leafLookup {n : ℕ} (get : Ref → Option (Row n)) (support : Weights)
    (extra : List (Row n)) : LeafRowRef → Option (Row n)
  | .original ref => get ref
  | .tight i negative => (tightRow get support i).map (fun r => if negative then negRow r else r)
  | .extra i => extra[i]?

private theorem leafLookup_valid {n : ℕ} {get : Ref → Option (Row n)} {support : Weights}
    {extra : List (Row n)} {g : Fin n → ℝ} (hv : Valid get g)
    (ht : supportTight get support g) (he : PathHolds extra g) :
    Valid (leafLookup get support extra) g := by
  intro ref r h
  cases ref with
  | original ref => exact hv ref r h
  | extra i => exact he r (List.mem_of_getElem? (show extra[i]? = some r from h))
  | tight i neg =>
    cases hr : tightRow get support i with
    | none => simp [leafLookup, hr] at h
    | some row =>
      have hEq := tightRow_eq ht hr
      cases neg with
      | false => have e : row = r := by simpa [leafLookup, hr] using h
                 exact e ▸ hEq.ge
      | true =>
        have e : negRow row = r := by simpa [leafLookup, hr] using h
        subst r
        unfold Row.Holds
        rw [negRow, eval_neg, hEq]
        simp [negRow]

-- Convert the local list to the existing nonnegative integer aggregate interface.
def contradiction {n : ℕ} (get : LeafRowRef → Option (Row n)) :
    List (LeafRowRef × ℤ) → Option (Row n)
  | [] => some (.zero n)
  | (ref, w) :: rest => do
    if w < 0 then none else
      let r ← get ref
      let s ← contradiction get rest
      pure (r.addScaled w s)

private theorem contradiction_holds {n : ℕ} {get : LeafRowRef → Option (Row n)} {g : Fin n → ℝ}
    (hv : Valid get g) {terms : List (LeafRowRef × ℤ)} {total : Row n}
    (hc : contradiction get terms = some total) : total.Holds g := by
  induction terms generalizing total with
  | nil =>
    have h : Row.zero n = total := Option.some.inj hc
    subst total
    simp [Row.Holds, Row.zero, eval]
  | cons term rest ih =>
    obtain ⟨ref, w⟩ := term
    by_cases hw : w < 0
    · simp [contradiction, hw] at hc
    cases hr : get ref with
    | none => simp [contradiction, hw, hr] at hc
    | some r =>
      cases hs : contradiction get rest with
      | none => simp [contradiction, hw, hr, hs] at hc
      | some s =>
        have h : r.addScaled w s = total := by simpa [contradiction, hw, hr, hs] using hc
        subst total
        change ((w * r.rhs + s.rhs : ℤ) : ℝ) ≤ eval (fun i => w * r.normal i + s.normal i) g
        rw [eval_add, eval_scale, Int.cast_add, Int.cast_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hv ref r hr) (by exact_mod_cast le_of_not_gt hw)) (ih hs)

abbrev PackTerm := ℕ × ℕ × ℤ

def packCombination {n : ℕ} (data : Array (Static n)) (support : Weights) :
    List PackTerm → Option (Fin n → ℤ)
  | [] => some (fun _ => 0)
  | (i, j, c) :: tail => do
    let (q, _) ← rankedSlot data support i j
    let a ← packCombination data support tail
    pure (fun t => c * q.normal t + a t)

private theorem packCombination_integral {n : ℕ} {data : Array (Static n)} {support : Weights}
    {path : List (Row n)} {g : Fin n → ℝ}
    (ht : supportTight (lookup (staticRows data) path) support g) (hg : Separated g)
    {terms : List PackTerm} {a : Fin n → ℤ}
    (hc : packCombination data support terms = some a) : IsIntegral (eval a g) := by
  induction terms generalizing a with
  | nil =>
    have he : (fun _ => (0 : ℤ)) = a := Option.some.inj hc
    subst a
    exact ⟨0, by simp [eval]⟩
  | cons item rest ih =>
    obtain ⟨i, j, c⟩ := item
    cases hp : rankedSlot data support i j with
    | none => simp [packCombination, hp] at hc
    | some pair =>
      obtain ⟨q, m⟩ := pair
      cases hs : packCombination data support rest with
      | none => simp [packCombination, hp, hs] at hc
      | some b =>
        have he : (fun t => c * q.normal t + b t) = a := by
          simpa [packCombination, hp, hs] using hc
        subst a
        obtain ⟨k, hk⟩ := rankedSlot_rank ht hg hp
        have hq : IsIntegral (eval q.normal g) :=
          ⟨(k.val : ℤ) + 1, by simpa using hk⟩
        rw [eval_add, eval_scale]
        exact (hq.zsmul c).add (ih hs)

structure GapCertificate where
  scale : ℕ
  constant : ℤ
  equalities : List (ℕ × ℤ)
  packing : List PackTerm

def checkGap {n : ℕ} (data : Array (Static n)) (get : Ref → Option (Row n))
    (support : Weights) (i : Fin n) (cert : GapCertificate) : Bool :=
  match affineCombination get support cert.equalities, packCombination data support cert.packing with
  | some total, some a =>
    decide (0 < cert.scale) &&
      (total.rhs == (cert.scale : ℤ) * cert.constant) &&
      (List.finRange n).all (fun j =>
        total.normal j == (cert.scale : ℤ) * ((if j = i then 1 else 0) - a j))
  | _, _ => false

private theorem checked_gap {n : ℕ} {data : Array (Static n)} {path : List (Row n)}
    {support : Weights} {g : Fin n → ℝ} {i : Fin n} {cert : GapCertificate}
    (ht : supportTight (lookup (staticRows data) path) support g) (hg : Separated g)
    (hc : checkGap data (lookup (staticRows data) path) support i cert = true) :
    IsIntegral (g i) := by
  cases hq : affineCombination (lookup (staticRows data) path) support cert.equalities with
  | none => simp [checkGap, hq] at hc
  | some total =>
    cases ha : packCombination data support cert.packing with
    | none => simp [checkGap, hq, ha] at hc
    | some a =>
      simp only [checkGap, hq, ha, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hp, hb⟩, hn⟩ := hc
      have hn' : total.normal = fun j => (cert.scale : ℤ) * ((if j = i then 1 else 0) - a j) :=
        funext (fun j => hn j (by simp))
      have hunit : eval (fun j => if j = i then 1 else 0) g = g i := by
        rw [eval, Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [hj]
        · simp
      have he := affine_combination_eq ht hq
      rw [hn', hb, eval_scale, eval_sub, hunit, Int.cast_mul, Int.cast_natCast] at he
      have hne : (cert.scale : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      have hid := mul_left_cancel₀ hne he
      have hz : IsIntegral ((cert.constant : ℝ) + eval a g) :=
        (show IsIntegral (cert.constant : ℝ) from ⟨_, rfl⟩).add (packCombination_integral ht hg ha)
      have hgap : g i = (cert.constant : ℝ) + eval a g := by linarith
      exact hgap ▸ hz

def slotLower {n : ℕ} (q : Span n) (b : ℤ) : Row n := ⟨q.normal, b⟩
def slotUpper {n : ℕ} (q : Span n) (b : ℤ) : Row n := negRow (slotLower q b)

private theorem slot_upper {n : ℕ} {q : Span n} {g : Fin n → ℝ} {b : ℤ}
    (h : eval q.normal g ≤ (b : ℝ)) : (slotUpper q b).Holds g := by
  unfold Row.Holds slotUpper
  rw [negRow, eval_neg]
  change ((-b : ℤ) : ℝ) ≤ -eval q.normal g
  push_cast
  exact neg_le_neg h

inductive LeafCertificate where
  | impossible (terms : List (LeafRowRef × ℤ))
  | integral (gaps : List GapCertificate)
  | relation (index : ℕ) (negative positive : LeafCertificate)
  | packRange (supportIndex slot : ℕ) (next : LeafCertificate)
  | packSplit (supportIndex slot cutoff : ℕ) (low high : LeafCertificate)

def LeafCertificate.check {n : ℕ} (data : Array (Static n))
    (relations : Array (Fin n → ℤ)) (get : Ref → Option (Row n)) (support : Weights)
    (extra : List (Row n)) : LeafCertificate → Bool
  | .impossible terms =>
    match contradiction (leafLookup get support extra) terms with
    | none => false
    | some r => checkFarkas r
  | .integral certs =>
    (List.finRange n).all (fun i =>
      match certs[i.val]? with
      | none => false
      | some cert => checkGap data get support i cert)
  | .relation i l r =>
    match relations[i]? with
    | none => false
    | some a => l.check data relations get support (extra ++ [branchRow false a]) &&
      r.check data relations get support (extra ++ [branchRow true a])
  | .packRange i j next =>
    match rankedSlot data support i j with
    | none => false
    | some (q, m) => next.check data relations get support
      ((extra ++ [slotLower q 1]) ++ [slotUpper q m])
  | .packSplit i j k l r =>
    match rankedSlot data support i j with
    | none => false
    | some (q, _) => l.check data relations get support (extra ++ [slotUpper q k]) &&
      r.check data relations get support (extra ++ [slotLower q (k + 1 : ℕ)])

private theorem LeafCertificate.sound {n : ℕ} {data : Array (Static n)}
    {relations : Array (Fin n → ℤ)} {path : List (Row n)} {support : Weights}
    {extra : List (Row n)} {cert : LeafCertificate} {g : Fin n → ℝ}
    (hg : Separated g) (hr : RelationsValid relations g)
    (hv : Valid (lookup (staticRows data) path) g)
    (ht : supportTight (lookup (staticRows data) path) support g) (he : PathHolds extra g)
    (hc : cert.check data relations (lookup (staticRows data) path) support extra = true) :
    IntegralGaps g := by
  induction cert generalizing extra with
  | impossible terms =>
    cases hs : contradiction (leafLookup (lookup (staticRows data) path) support extra) terms with
    | none => simp [LeafCertificate.check, hs] at hc
    | some total =>
      have hf : checkFarkas total = true := by simpa [LeafCertificate.check, hs] using hc
      exact False.elim (checked_farkas hf (contradiction_holds (leafLookup_valid hv ht he) hs))
  | integral certs =>
    intro i
    have hi := List.all_eq_true.mp hc i (by simp)
    cases hh : certs[i.val]? with
    | none => simp [hh] at hi
    | some c => exact checked_gap ht hg (by simpa [hh] using hi)
  | relation i l r ihl ihr =>
    cases ha : relations[i]? with
    | none => simp [LeafCertificate.check, ha] at hc
    | some a =>
      simp only [LeafCertificate.check, ha, Bool.and_eq_true] at hc
      rcases branch_cover (hr i a ha) with hl | hright
      · exact ihl (pathHolds_append he hl) hc.1
      · exact ihr (pathHolds_append he hright) hc.2
  | packRange i j next ih =>
    cases hs : rankedSlot data support i j with
    | none => simp [LeafCertificate.check, hs] at hc
    | some pair =>
      obtain ⟨q, m⟩ := pair
      obtain ⟨k, hk⟩ := rankedSlot_rank ht hg hs
      have hlow : (slotLower q 1).Holds g := by
        change ((1 : ℤ) : ℝ) ≤ eval q.normal g
        push_cast
        rw [hk]
        exact le_add_of_nonneg_left (by positivity)
      have hkm : (k.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast k.isLt
      have hhigh : (slotUpper q m).Holds g := slot_upper (by rw [hk]; simpa using hkm)
      exact ih (pathHolds_append (pathHolds_append he hlow) hhigh)
        (by simpa [LeafCertificate.check, hs] using hc)
  | packSplit i j cutoff l r ihl ihr =>
    cases hs : rankedSlot data support i j with
    | none => simp [LeafCertificate.check, hs] at hc
    | some pair =>
      obtain ⟨q, m⟩ := pair
      obtain ⟨k, hk⟩ := rankedSlot_rank ht hg hs
      simp only [LeafCertificate.check, hs, Bool.and_eq_true] at hc
      by_cases hb : k.val < cutoff
      · have hu : (k.val : ℝ) + 1 ≤ (cutoff : ℝ) := by exact_mod_cast hb
        have hrow : (slotUpper q cutoff).Holds g := slot_upper (by rw [hk]; simpa using hu)
        exact ihl (pathHolds_append he hrow) hc.1
      · have hl : (cutoff : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast Nat.le_of_not_gt hb
        have hrow : (slotLower q (cutoff + 1 : ℕ)).Holds g := by
          change (((cutoff + 1 : ℕ) : ℤ) : ℝ) ≤ eval q.normal g
          rw [hk]
          push_cast
          linarith
        exact ihr (pathHolds_append he hrow) hc.2

def directLookup {n : ℕ} (data : Array (Static n)) (path : List (Row n)) :
    Ref → Option (Row n)
  | .static i => data[i]?.map Static.row
  | .branch i => path[i]?

private theorem directLookup_eq {n : ℕ} (data : Array (Static n)) (path : List (Row n)) :
    directLookup data path = lookup (staticRows data) path := by
  funext r
  cases r <;> simp [directLookup, lookup, staticRows]

def totalRhs {n : ℕ} (data : Array (Static n)) : Weights → Option ℤ
  | [] => some 0
  | (ref, w) :: tail => do
    let b ← match ref with
      | .static i => data[i]?.map (fun s => s.row.rhs)
      | .branch _ => some 1
    let more ← totalRhs data tail
    pure (w * b + more)

private theorem totalRhs_eq {n : ℕ} {data : Array (Static n)} {path : List (Row n)}
    {weights : Weights} {total : Row n} (hp : ∀ r ∈ path, r.rhs = 1)
    (ha : aggregate (lookup (staticRows data) path) weights = some total) :
    totalRhs data weights = some total.rhs := by
  induction weights generalizing total with
  | nil =>
    have he : Row.zero n = total := Option.some.inj ha
    subst total
    rfl
  | cons item rest ih =>
    obtain ⟨ref, w⟩ := item
    by_cases hw : w < 0
    · simp [aggregate, hw] at ha
    cases hrow : lookup (staticRows data) path ref with
    | none => simp [aggregate, hw, hrow] at ha
    | some r =>
      cases htail : aggregate (lookup (staticRows data) path) rest with
      | none => simp [aggregate, hw, hrow, htail] at ha
      | some s =>
        have he : r.addScaled w s = total := by simpa [aggregate, hw, hrow, htail] using ha
        subst total
        cases ref with
        | static i =>
          rw [← directLookup_eq] at hrow
          simp only [directLookup] at hrow
          cases h : data[i]? with
          | none => simp [h] at hrow
          | some row =>
            have he : row.row = r := by simpa [h] using hrow
            simp [totalRhs, h, he, ih htail, Row.addScaled]
        | branch i =>
          have hvalue : r.rhs = 1 := hp r (List.mem_of_getElem? hrow)
          simp [totalRhs, hvalue, ih htail, Row.addScaled]

abbrev LeafTable := List (ℕ × LeafCertificate)

/-- In tree traversal order consume exactly one entry per equality-capable
bound leaf. Strict leaves consume no entry. The equality route comes from the
independently proved lower-bound replay. -/
def Tree.cover {n : ℕ} (target : ℤ) (data : Array (Static n))
    (witnesses : Array (RelationWitness n)) (path : List (Row n)) :
    Tree → LeafTable → Option LeafTable
  | .farkas _ _, table => some table
  | .bound id scale weights, table => do
    let rhs ← totalRhs data weights
    if rhs = (scale : ℤ) * target then
      match table with
      | (key, cert) :: tail =>
        if key == id && cert.check data (relationRows witnesses) (directLookup data path) weights [] then
          some tail
        else none
      | [] => none
    else some table
  | .branch _ i left right, table => do
    let witness ← witnesses[i]?
    let next ← left.cover target data witnesses (path ++ [branchRow false witness.normal]) table
    right.cover target data witnesses (path ++ [branchRow true witness.normal]) next

def finishedCover : Option LeafTable → Bool
  | some [] => true
  | _ => false

theorem finishedCover_sound {tail : Option LeafTable} (h : finishedCover tail = true) :
    tail = some [] := by
  cases tail with
  | none => simp [finishedCover] at h
  | some xs =>
    cases xs with
    | nil => rfl
    | cons => simp [finishedCover] at h

private theorem Tree.Routes.covered_integral {n : ℕ} {target : ℤ} {data : Array (Static n)}
    {witnesses : Array (RelationWitness n)} {g : Fin n → ℝ} {path leafPath : List (Row n)}
    {tree : Tree} {id scale : ℕ} {weights : Weights} {total : Row n}
    (route : tree.Routes (relationRows witnesses) g path leafPath (.bound id scale weights))
    (hg : Separated g) (hr : RelationsValid (relationRows witnesses) g)
    (hv : Valid (fun i : ℕ => (staticRows data)[i]?) g) (hl : PathHolds leafPath g)
    (ha : aggregate (lookup (staticRows data) leafPath) weights = some total)
    (he : total.rhs = (scale : ℤ) * target)
    (ht : supportTight (lookup (staticRows data) leafPath) weights g)
    (hp : ∀ r ∈ path, r.rhs = 1)
    {table tail : LeafTable} (hc : tree.cover target data witnesses path table = some tail) :
    IntegralGaps g := by
  generalize hleaf : Tree.bound id scale weights = terminal at route
  induction route generalizing table tail with
  | stop path key s ws =>
    cases hleaf
    have hRhs := totalRhs_eq hp ha
    cases table with
    | nil => simp [Tree.cover, hRhs, he] at hc
    | cons entry rest =>
      obtain ⟨ek, cert⟩ := entry
      have hcert : cert.check data (relationRows witnesses) (directLookup data path) weights [] = true := by
        by_contra hn
        have hf : cert.check data (relationRows witnesses) (directLookup data path) weights [] = false :=
          Bool.eq_false_iff.mpr hn
        simp [Tree.cover, hRhs, he, hf] at hc
      rw [directLookup_eq] at hcert
      exact LeafCertificate.sound hg hr (lookup_valid hv hl) ht
        (show PathHolds ([] : List (Row n)) g by simp [PathHolds]) hcert
  | @negative path final leaf left right key i a hrel _ _ ih =>
    have hp' : ∀ r ∈ path ++ [branchRow false a], r.rhs = 1 := by
      intro r h
      rcases List.mem_append.mp h with h | h
      · exact hp r h
      · rcases List.mem_singleton.mp h with rfl
        rfl
    rw [relationRows, Array.getElem?_map] at hrel
    cases hw : witnesses[i]? with
    | none => simp [hw] at hrel
    | some w =>
      have hnormal : w.normal = a := by simpa [hw] using hrel
      subst a
      cases hleft : left.cover target data witnesses (path ++ [branchRow false w.normal]) table with
      | none => simp [Tree.cover, hw, hleft] at hc
      | some next => apply ih <;> assumption
  | @positive path final leaf left right key i a hrel _ _ ih =>
    have hp' : ∀ r ∈ path ++ [branchRow true a], r.rhs = 1 := by
      intro r h
      rcases List.mem_append.mp h with h | h
      · exact hp r h
      · rcases List.mem_singleton.mp h with rfl
        rfl
    rw [relationRows, Array.getElem?_map] at hrel
    cases hw : witnesses[i]? with
    | none => simp [hw] at hrel
    | some w =>
      have hnormal : w.normal = a := by simpa [hw] using hrel
      subst a
      cases hleft : left.cover target data witnesses (path ++ [branchRow false w.normal]) table with
      | none => simp [Tree.cover, hw, hleft] at hc
      | some next =>
        have hright : right.cover target data witnesses (path ++ [branchRow true w.normal]) next = some tail :=
          by simpa [Tree.cover, hw, hleft] using hc
        apply ih <;> assumption

private theorem marks_integral_of_gaps {n : ℕ} {x : Marks n} (hzero : x 0 = 0)
    (hg : IntegralGaps (gaps x)) : ∀ i, ∃ z : ℤ, x i = (z : ℝ) := by
  intro i
  have hp := prefix_gaps x i
  rw [hzero, sub_zero] at hp
  rw [← hp]
  unfold positions eval
  choose z hz using hg
  simp only [hz]
  refine ⟨∑ j : Fin n, (if j.val < i.val then 1 else 0) * z j, ?_⟩
  push_cast
  rfl

theorem replay_marks_integral {k : ℕ} {target : ℤ} {bounds : ℕ → ℤ}
    {data : Array (Static (k + 2))} {witnesses : Array (RelationWitness (k + 2))}
    {tree : Tree} {table : LeafTable}
    (hb : SmallerBounds (k + 2) bounds) (hs : checkStatic data bounds = true)
    (ht : tree.check target (staticRows data) (relationRows witnesses) [] = true)
    (hc : tree.cover target data witnesses [] table = some [])
    {x : Marks (k + 2)} (hx : RealGolomb x) (hzero : x 0 = 0)
    (hlen : endLength x = (target : ℝ)) :
    ∀ i, ∃ z : ℤ, x i = (z : ℝ) := by
  have run (y : Marks (k + 2)) (hy : RealGolomb y) (ho : Oriented (gaps y))
      (he : endLength y = (target : ℝ)) : IntegralGaps (gaps y) := by
    have hg := separated_gaps hy
    have hv := staticRows_valid data hb hs hg ho
    have hr := relationRows_valid witnesses hg
    obtain ⟨p, i, s, w, t, route, hpath, ha, _, heq, hsupport⟩ :=
      (Tree.check_sound ht hv hr (by simp [PathHolds])).2 ((length_gaps y).trans he)
    exact route.covered_integral hg hr hv hpath ha heq hsupport (by simp) hc
  apply marks_integral_of_gaps hzero
  rcases symmetry_coverage hx with ho | ho
  · exact run x hx ho hlen
  · have hi := run (reflect x) (reflect_golomb hx) ho ((reflect_length x).trans hlen)
    intro i
    simpa only [reflect_gaps, Fin.rev_rev] using hi i.rev

end D5.S3.Combinatorics.Golomb.Replay
