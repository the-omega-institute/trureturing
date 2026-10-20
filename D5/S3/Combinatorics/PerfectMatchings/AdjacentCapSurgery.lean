/- GID: D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Adjacent cap removal in a noncrossing matching. -/
import D5.S3.Combinatorics.PerfectMatchings.OrderedMatchingIntervals

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CupCapBridgeProposal

/-- All eight orientations of strict alternation between two unoriented arcs. -/
def NoInterleave (a b c d : ℕ) : Prop :=
  ¬ (a < c ∧ c < b ∧ b < d) ∧
  ¬ (c < a ∧ a < d ∧ d < b) ∧
  ¬ (a < d ∧ d < b ∧ b < c) ∧
  ¬ (d < a ∧ a < c ∧ c < b) ∧
  ¬ (b < c ∧ c < a ∧ a < d) ∧
  ¬ (c < b ∧ b < d ∧ d < a) ∧
  ¬ (b < d ∧ d < a ∧ a < c) ∧
  ¬ (d < b ∧ b < c ∧ c < a)

namespace NCMatching
variable {n : ℕ} (M : NCMatching n)

/-- The original crossing prohibition with all arc orientations made explicit. -/
theorem arcs_no_interleave (a c : Fin n) :
    NoInterleave a.val (M.partner a).val c.val (M.partner c).val := by
  have h₁ := M.noncrossing a c
  have h₂ := M.noncrossing c a
  have h₃ := M.noncrossing a (M.partner c)
  have h₄ := M.noncrossing (M.partner c) a
  have h₅ := M.noncrossing (M.partner a) c
  have h₆ := M.noncrossing c (M.partner a)
  have h₇ := M.noncrossing (M.partner a) (M.partner c)
  have h₈ := M.noncrossing (M.partner c) (M.partner a)
  rw [M.involutive c] at h₃ h₄ h₇ h₈
  rw [M.involutive a] at h₅ h₆ h₇ h₈
  unfold NoInterleave
  change (a.val < c.val → c.val < (M.partner a).val →
    (M.partner a).val < (M.partner c).val → False) at h₁
  change (c.val < a.val → a.val < (M.partner c).val →
    (M.partner c).val < (M.partner a).val → False) at h₂
  simp only [Fin.lt_def] at h₃ h₄ h₅ h₆ h₇ h₈
  constructor
  · rintro ⟨h₁a, h₁b, h₁c⟩
    exact h₁ h₁a h₁b h₁c
  constructor
  · rintro ⟨h₂a, h₂b, h₂c⟩
    exact h₂ h₂a h₂b h₂c
  constructor
  · rintro ⟨h₃a, h₃b, h₃c⟩
    exact h₃ h₃a h₃b h₃c
  constructor
  · rintro ⟨h₄a, h₄b, h₄c⟩
    exact h₄ h₄a h₄b h₄c
  constructor
  · rintro ⟨h₅a, h₅b, h₅c⟩
    exact h₅ h₅a h₅b h₅c
  constructor
  · rintro ⟨h₆a, h₆b, h₆c⟩
    exact h₆ h₆a h₆b h₆c
  constructor
  · rintro ⟨h₇a, h₇b, h₇c⟩
    exact h₇ h₇a h₇b h₇c
  · rintro ⟨h₈a, h₈b, h₈c⟩
    exact h₈ h₈a h₈b h₈c
end NCMatching

set_option maxHeartbeats 10000000 in
theorem adjacent_reconnect_no_interleave {a b u v x z : ℕ}
    (hab : b = a + 1) (hua : u ≠ a) (hvb : v ≠ b)
    (hub : u ≠ b) (hva : v ≠ a) (huv : u ≠ v)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxu : x ≠ u) (hxv : x ≠ v)
    (hza : z ≠ a) (hzb : z ≠ b) (hzu : z ≠ u) (hzv : z ≠ v)
    (hxz : x ≠ z)
    (horder : u = b ∨ (u < a ∧ b < v) ∨ (b < v ∧ v < u) ∨
      (v < u ∧ u < a))
    (hold : NoInterleave a u b v)
    (hleft : NoInterleave a u x z)
    (hright : NoInterleave b v x z) : NoInterleave u v x z := by
  unfold NoInterleave at hleft hright ⊢
  rcases hleft with ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8⟩
  rcases hright with ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩
  rcases horder with hclose | hsib | hleftOrder | hrightOrder
  · exact False.elim (hub hclose)
  · rcases hsib with ⟨hsib1, hsib2⟩
    clear hold hua hvb hub hva huv hxu hxv hzu hzv hxz
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      have hor : (u < x ∧ x < a ∧ a < z) ∨ (b < x ∧ x < v ∧ v < z) := by
        by_cases hx : x < a
        · left; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
        · right; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
      rcases hor with hL | hR
      · exact hl5 hL
      · exact hr1 hR
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      have hor : (x < u ∧ u < z ∧ z < a) ∨ (x < b ∧ b < z ∧ z < v) := by
        by_cases hh : z < a
        · left; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
        · right; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
      rcases hor with hL | hR
      · exact hl6 hL
      · exact hr2 hR
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      have hor : (u < z ∧ z < a ∧ a < x) ∨ (b < z ∧ z < v ∧ v < x) := by
        by_cases hz : z < a
        · left; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
        · right; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
      rcases hor with hL | hR
      · exact hl7 hL
      · exact hr3 hR
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      have hor : (z < u ∧ u < x ∧ x < a) ∨ (z < b ∧ b < x ∧ x < v) := by
        by_cases hh : x < a
        · left; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
        · right; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
      rcases hor with hL | hR
      · exact hl8 hL
      · exact hr4 hR
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
  · rcases hleftOrder with ⟨hleft1, hleft2⟩
    clear hold hua hvb hub hva huv hxu hxv hzu hzv hxz
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      exact hl1 ⟨by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega, by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega, by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega⟩
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      have hor : (x < a ∧ a < z ∧ z < u) ∨ (b < x ∧ x < v ∧ v < z) := by
        by_cases hx : x < a
        · left; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
        · right; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
      rcases hor with hL | hR
      · exact hl2 hL
      · exact hr1 hR
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      exact hl3 ⟨by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega, by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega, by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega⟩
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      have hor : (z < a ∧ a < x ∧ x < u) ∨ (b < z ∧ z < v ∧ v < x) := by
        by_cases hh : z < a
        · left; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
        · right; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
      rcases hor with hL | hR
      · exact hl4 hL
      · exact hr3 hR
  · rcases hrightOrder with ⟨hright1, hright2⟩
    clear hold hua hvb hub hva huv hxu hxv hzu hzv hxz
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
      omega
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      have hor : (x < u ∧ u < z ∧ z < a) ∨ (v < x ∧ x < b ∧ b < z) := by
        by_cases hz : z < a
        · left; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
        · right; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
      rcases hor with hL | hR
      · exact hl6 hL
      · exact hr5 hR
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      exact hr6 ⟨by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega, by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega, by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega⟩
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      have hor : (z < u ∧ u < x ∧ x < a) ∨ (v < z ∧ z < b ∧ b < x) := by
        by_cases hx : x < a
        · left; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
        · right; constructor <;> (clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega)
      rcases hor with hL | hR
      · exact hl8 hL
      · exact hr7 hR
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      exact hr8 ⟨by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega, by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega, by clear hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8; omega⟩

section Skip
variable {m : ℕ} (j : Fin (m + 1))

theorem skipPair_strictMono : StrictMono (skipPair j) := by
  intro k l hkl
  change insertPort j.val k.val < insertPort j.val l.val
  unfold insertPort
  split_ifs <;> omega

theorem skipPair_injective : Function.Injective (skipPair j) :=
  (skipPair_strictMono j).injective

theorem skipPair_survives (k : Fin m) :
    skipPair j k ≠ j.castSucc ∧ skipPair j k ≠ j.succ := by
  constructor <;> intro h <;>
    have he := congrArg Fin.val h <;>
    simp only [skipPair, insertPort, Fin.val_mk, Fin.val_castSucc, Fin.val_succ] at he <;>
    split_ifs at he <;> omega

/-- The inverse is defined only on the actual surviving endpoints. -/
def unskipPair (k : Fin (m + 2)) (ha : k ≠ j.castSucc) (hb : k ≠ j.succ) : Fin m :=
  ⟨if k.val < j.val then k.val else k.val - 2, by
    have hk := k.isLt
    have hj := j.isLt
    have hka : k.val ≠ j.val := fun h => ha (Fin.ext h)
    have hkb : k.val ≠ j.val + 1 := fun h => hb (Fin.ext h)
    split_ifs <;> omega⟩

theorem skipPair_unskipPair (k : Fin (m + 2))
    (ha : k ≠ j.castSucc) (hb : k ≠ j.succ) :
    skipPair j (unskipPair j k ha hb) = k := by
  apply Fin.ext
  have hka : k.val ≠ j.val := fun h => ha (Fin.ext h)
  have hkb : k.val ≠ j.val + 1 := fun h => hb (Fin.ext h)
  simp only [skipPair, unskipPair, insertPort, Fin.val_mk]
  split_ifs <;> omega

theorem unskipPair_skipPair (k : Fin m) :
    unskipPair j (skipPair j k) (skipPair_survives j k).1
      (skipPair_survives j k).2 = k := by
  apply skipPair_injective j
  exact skipPair_unskipPair j _ _ _

/-- Ordered enumeration of the complement of exactly the two consumed ends. -/
def survivorEquiv : Fin m ≃ {k : Fin (m + 2) // k ≠ j.castSucc ∧ k ≠ j.succ} where
  toFun k := ⟨skipPair j k, skipPair_survives j k⟩
  invFun k := unskipPair j k.val k.property.1 k.property.2
  left_inv := unskipPair_skipPair j
  right_inv k := Subtype.ext (skipPair_unskipPair j k.val k.property.1 k.property.2)
end Skip

section Surgery
variable {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1))

/-- S P S, with S swapping b and P(a); the close case has S = identity. -/
def capConjugate : Equiv.Perm (Fin (m + 2)) :=
  Equiv.swap j.succ (M.partner j.castSucc) * M.partner *
    Equiv.swap j.succ (M.partner j.castSucc)

theorem capConjugate_apply (k : Fin (m + 2)) :
    capConjugate M j k =
      Equiv.swap j.succ (M.partner j.castSucc)
        (M.partner (Equiv.swap j.succ (M.partner j.castSucc) k)) := rfl

theorem capConjugate_involutive : Function.Involutive (capConjugate M j) := by
  intro k
  let b := j.succ
  let u := M.partner j.castSucc
  change Equiv.swap b u
    (M.partner (Equiv.swap b u
      (Equiv.swap b u (M.partner (Equiv.swap b u k))))) = k
  rw [Equiv.swap_apply_self, M.involutive, Equiv.swap_apply_self]

theorem capConjugate_noFixed (k : Fin (m + 2)) : capConjugate M j k ≠ k := by
  intro he
  apply M.noFixed (Equiv.swap j.succ (M.partner j.castSucc) k)
  have h := congrArg (Equiv.swap j.succ (M.partner j.castSucc)) he
  simpa only [capConjugate_apply, Equiv.swap_apply_self] using h

theorem capConjugate_left : capConjugate M j j.castSucc = j.succ := by
  have hab : j.castSucc ≠ j.succ := by
    intro h
    have he := congrArg Fin.val h
    have hj := j.isLt
    simp only [Fin.val_castSucc, Fin.val_succ] at he
    omega
  have hau : j.castSucc ≠ M.partner j.castSucc := (M.noFixed _).symm
  rw [capConjugate_apply, Equiv.swap_apply_of_ne_of_ne hab hau,
    Equiv.swap_apply_right]

theorem capConjugate_right : capConjugate M j j.succ = j.castSucc := by
  have h := capConjugate_involutive M j j.castSucc
  rw [capConjugate_left] at h
  exact h

/-- Exact equality to the dispatch's reconnectPartner on its intended domain. -/
theorem capConjugate_reconnect (k : Fin (m + 2))
    (hka : k ≠ j.castSucc) (hkb : k ≠ j.succ) :
    capConjugate M j k = reconnectPartner M j k := by
  let a := j.castSucc
  let b := j.succ
  let u := M.partner a
  let v := M.partner b
  have hab : a ≠ b := by
    intro h
    have he := congrArg Fin.val h
    simp only [a, b, Fin.val_castSucc, Fin.val_succ] at he
    omega
  have huv : u ≠ v := fun h => hab (M.partner.injective h)
  by_cases hpa : M.partner k = a
  · have hku : k = u := by
      have h := congrArg M.partner hpa
      calc
        k = M.partner (M.partner k) := (M.involutive _).symm
        _ = M.partner a := h
        _ = u := rfl
    have hvb : v ≠ b := M.noFixed b
    have hvu : v ≠ u := huv.symm
    change Equiv.swap b u (M.partner (Equiv.swap b u k)) =
      (if M.partner k = a then v else if M.partner k = b then u else M.partner k)
    rw [if_pos hpa, hku, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hvb hvu]
  · by_cases hpb : M.partner k = b
    · have hkv : k = v := by
        have h := congrArg M.partner hpb
        calc
          k = M.partner (M.partner k) := (M.involutive _).symm
          _ = M.partner b := h
          _ = v := rfl
      have hvb : v ≠ b := M.noFixed b
      have hvu : v ≠ u := huv.symm
      change Equiv.swap b u (M.partner (Equiv.swap b u k)) =
        (if M.partner k = a then v else if M.partner k = b then u else M.partner k)
      rw [if_neg hpa, if_pos hpb, hkv,
        Equiv.swap_apply_of_ne_of_ne hvb hvu, M.involutive,
        Equiv.swap_apply_left]
    · have hku : k ≠ u := by
        intro h
        apply hpa
        simpa only [h, u, M.involutive] using M.involutive a
      have hpu : M.partner k ≠ u := by
        intro h
        apply hka
        exact M.partner.injective h
      change Equiv.swap b u (M.partner (Equiv.swap b u k)) =
        (if M.partner k = a then v else if M.partner k = b then u else M.partner k)
      rw [if_neg hpa, if_neg hpb,
        Equiv.swap_apply_of_ne_of_ne hkb hku,
        Equiv.swap_apply_of_ne_of_ne hpb hpu]

theorem capConjugate_survives (k : Fin (m + 2))
    (hka : k ≠ j.castSucc) (hkb : k ≠ j.succ) :
    capConjugate M j k ≠ j.castSucc ∧ capConjugate M j k ≠ j.succ := by
  constructor
  · intro h
    apply hkb
    exact (capConjugate M j).injective (h.trans (capConjugate_right M j).symm)
  · intro h
    apply hka
    exact (capConjugate M j).injective (h.trans (capConjugate_left M j).symm)

/-- Restriction of the concrete conjugate permutation to its invariant complement. -/
def survivorPartner : Equiv.Perm {k : Fin (m + 2) // k ≠ j.castSucc ∧ k ≠ j.succ} where
  toFun k := ⟨capConjugate M j k.val,
    capConjugate_survives M j k.val k.property.1 k.property.2⟩
  invFun k := ⟨capConjugate M j k.val,
    capConjugate_survives M j k.val k.property.1 k.property.2⟩
  left_inv k := Subtype.ext (capConjugate_involutive M j k.val)
  right_inv k := Subtype.ext (capConjugate_involutive M j k.val)

/-- Transport is through the actual ordered skipPair enumeration. -/
def capPartner : Equiv.Perm (Fin m) :=
  (survivorEquiv j).trans ((survivorPartner M j).trans (survivorEquiv j).symm)

theorem skipPair_capPartner (k : Fin m) :
    skipPair j (capPartner M j k) = reconnectPartner M j (skipPair j k) := by
  let z := (survivorPartner M j) ((survivorEquiv j) k)
  have hza := z.property.1
  have hzb := z.property.2
  have hz : skipPair j (unskipPair j z.val hza hzb) = z.val :=
    skipPair_unskipPair j z.val hza hzb
  change skipPair j (unskipPair j z.val hza hzb) = _
  rw [hz]
  exact capConjugate_reconnect M j _ (skipPair_survives j k).1
    (skipPair_survives j k).2

theorem capPartner_involutive : Function.Involutive (capPartner M j) := by
  intro k
  apply skipPair_injective j
  change (survivorEquiv j (capPartner M j (capPartner M j k))).val =
    (survivorEquiv j k).val
  simp only [capPartner, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact capConjugate_involutive M j _

theorem capPartner_noFixed (k : Fin m) : capPartner M j k ≠ k := by
  intro he
  have hv := congrArg (fun z => (survivorEquiv j z).val) he
  simp only [capPartner, Equiv.trans_apply, Equiv.apply_symm_apply] at hv
  change capConjugate M j (skipPair j k) = skipPair j k at hv
  exact capConjugate_noFixed M j _ hv

/-- The four complete orders, without a label or weight hypothesis. -/
theorem cap_order_cases :
    M.partner j.castSucc = j.succ ∨
    (M.partner j.castSucc < j.castSucc ∧ j.succ < M.partner j.succ) ∨
    (j.succ < M.partner j.succ ∧ M.partner j.succ < M.partner j.castSucc) ∨
    (M.partner j.succ < M.partner j.castSucc ∧ M.partner j.castSucc < j.castSucc) := by
  let a := j.castSucc
  let b := j.succ
  let u := M.partner a
  let v := M.partner b
  have hua : u ≠ a := M.noFixed a
  have hvb : v ≠ b := M.noFixed b
  have huv : u ≠ v := by
    intro h
    have he := congrArg Fin.val (M.partner.injective h)
    simp only [a, b, Fin.val_castSucc, Fin.val_succ] at he
    omega
  have hc := M.arcs_no_interleave a b
  change NoInterleave a.val u.val b.val v.val at hc
  have hab : b.val = a.val + 1 := rfl
  have hvua : v = a ↔ u = b := by
    constructor
    · intro he
      have h := congrArg M.partner he
      have h' : b = u := by
        calc
          b = M.partner (M.partner b) := (M.involutive _).symm
          _ = M.partner a := h
          _ = u := rfl
      exact h'.symm
    · intro he
      have h := congrArg M.partner he
      have h' : a = v := by
        calc
          a = M.partner (M.partner a) := (M.involutive _).symm
          _ = M.partner b := h
          _ = v := rfl
      exact h'.symm
  change u = b ∨ (u < a ∧ b < v) ∨ (b < v ∧ v < u) ∨ (v < u ∧ u < a)
  unfold NoInterleave at hc
  simp only [Fin.lt_def, Fin.ext_iff] at *
  omega

set_option maxHeartbeats 1000000 in
theorem reconnected_arc_no_interleave (hnclose : M.partner j.castSucc ≠ j.succ)
    (t : Fin (m + 2)) (hta : t ≠ j.castSucc) (htb : t ≠ j.succ)
    (htu : t ≠ M.partner j.castSucc) (htv : t ≠ M.partner j.succ) :
    NoInterleave (M.partner j.castSucc).val (M.partner j.succ).val
      t.val (M.partner t).val := by
  let a := j.castSucc
  let b := j.succ
  let u := M.partner a
  let v := M.partner b
  let z := M.partner t
  have hab : b.val = a.val + 1 := rfl
  have habFin : a ≠ b := by
    intro h
    have he := congrArg Fin.val h
    simp only [a, b, Fin.val_castSucc, Fin.val_succ] at he
    omega
  have hua : u.val ≠ a.val := by
    intro h
    apply M.noFixed a
    exact Fin.ext h
  have hvb : v.val ≠ b.val := by
    intro h
    apply M.noFixed b
    exact Fin.ext h
  have hub : u.val ≠ b.val := by
    intro h
    apply hnclose
    exact Fin.ext h
  have hva : v.val ≠ a.val := by
    intro h
    apply hnclose
    have hp := congrArg M.partner (Fin.ext h)
    calc
      M.partner a = M.partner (M.partner b) := hp.symm
      _ = b := M.involutive _
  have huv : u.val ≠ v.val := by
    intro h
    apply habFin
    exact M.partner.injective (Fin.ext h)
  have hxa : t.val ≠ a.val := by
    intro h
    exact hta (Fin.ext h)
  have hxb : t.val ≠ b.val := by
    intro h
    exact htb (Fin.ext h)
  have hxu : t.val ≠ u.val := by
    intro h
    exact htu (Fin.ext h)
  have hxv : t.val ≠ v.val := by
    intro h
    exact htv (Fin.ext h)
  have hza : z.val ≠ a.val := by
    intro h
    apply htu
    calc
      t = M.partner (M.partner t) := (M.involutive _).symm
      _ = M.partner a := congrArg M.partner (Fin.ext h)
      _ = u := rfl
  have hzb : z.val ≠ b.val := by
    intro h
    apply htv
    calc
      t = M.partner (M.partner t) := (M.involutive _).symm
      _ = M.partner b := congrArg M.partner (Fin.ext h)
      _ = v := rfl
  have hzu : z.val ≠ u.val := by
    intro h
    apply hta
    calc
      t = M.partner (M.partner t) := (M.involutive _).symm
      _ = M.partner u := congrArg M.partner (Fin.ext h)
      _ = a := M.involutive _
  have hzv : z.val ≠ v.val := by
    intro h
    apply htb
    calc
      t = M.partner (M.partner t) := (M.involutive _).symm
      _ = M.partner v := congrArg M.partner (Fin.ext h)
      _ = b := M.involutive _
  have hxz : t.val ≠ z.val := by
    intro h
    apply M.noFixed t
    exact (Fin.ext h).symm
  have hold := M.arcs_no_interleave a b
  have hleftArc := M.arcs_no_interleave a t
  have hrightArc := M.arcs_no_interleave b t
  have horder : u.val = b.val ∨
      (u.val < a.val ∧ b.val < v.val) ∨
      (b.val < v.val ∧ v.val < u.val) ∨
      (v.val < u.val ∧ u.val < a.val) := by
    rcases cap_order_cases M j with h | h | h | h
    · left
      change u = b at h
      exact congrArg Fin.val h
    · right; left
      rcases h with ⟨h1, h2⟩
      constructor
      · change u.val < a.val at h1
        exact h1
      · change b.val < v.val at h2
        exact h2
    · right; right; left
      rcases h with ⟨h1, h2⟩
      constructor
      · change b.val < v.val at h1
        exact h1
      · change v.val < u.val at h2
        exact h2
    · right; right; right
      rcases h with ⟨h1, h2⟩
      constructor
      · change v.val < u.val at h1
        exact h1
      · change u.val < a.val at h2
        exact h2
  change NoInterleave u.val v.val t.val z.val
  apply adjacent_reconnect_no_interleave hab hua hvb hub hva huv hxa hxb hxu hxv hza hzb hzu hzv hxz horder
  · exact hold
  · exact hleftArc
  · exact hrightArc

/-- Crossing preservation is paid here, independently of conjugation. -/
theorem reconnect_noncrossing (x y : Fin (m + 2))
    (hxa : x ≠ j.castSucc) (hxb : x ≠ j.succ)
    (hya : y ≠ j.castSucc) (hyb : y ≠ j.succ)
    (hxy : x < y) (hyx : y < reconnectPartner M j x)
    (hends : reconnectPartner M j x < reconnectPartner M j y) : False := by
  let a := j.castSucc
  let b := j.succ
  let u := M.partner a
  let v := M.partner b
  have hab : a ≠ b := by
    intro h
    have he := congrArg Fin.val h
    simp only [a, b, Fin.val_castSucc, Fin.val_succ] at he
    omega
  have hru : reconnectPartner M j u = v := by
    change (if M.partner u = a then v else
      if M.partner u = b then u else M.partner u) = v
    have hup : M.partner u = a := M.involutive a
    rw [hup, if_pos rfl]
  have hrv : reconnectPartner M j v = u := by
    change (if M.partner v = a then v else
      if M.partner v = b then u else M.partner v) = u
    have hvp : M.partner v = b := M.involutive b
    rw [hvp, if_neg hab.symm, if_pos rfl]
  have hrt (t : Fin (m + 2)) (htu : t ≠ u) (htv : t ≠ v) :
      reconnectPartner M j t = M.partner t := by
    have hta : M.partner t ≠ a := by
      intro he; apply htu
      calc
        t = M.partner (M.partner t) := (M.involutive _).symm
        _ = M.partner a := congrArg M.partner he
    have htb : M.partner t ≠ b := by
      intro he; apply htv
      calc
        t = M.partner (M.partner t) := (M.involutive _).symm
        _ = M.partner b := congrArg M.partner he
    change (if M.partner t = a then v else
      if M.partner t = b then u else M.partner t) = M.partner t
    rw [if_neg hta, if_neg htb]
  have hn_from_u (hu : u ≠ b) : M.partner j.castSucc ≠ j.succ := hu
  have hn_from_v (hv : v ≠ a) : M.partner j.castSucc ≠ j.succ := by
    intro he
    apply hv
    have hp := congrArg M.partner he
    calc
      v = M.partner b := rfl
      _ = M.partner (M.partner a) := hp.symm
      _ = a := M.involutive _
  by_cases hxu : x = u
  · subst x
    rw [hru] at hyx hends
    by_cases hyu : y = u
    · subst y; exact (lt_irrefl _) hxy
    by_cases hyv : y = v
    · subst y; exact (lt_irrefl _) hyx
    rw [hrt y hyu hyv] at hends
    have hc := reconnected_arc_no_interleave M j (hn_from_u hxb) y hya hyb hyu hyv
    simp only [Fin.lt_def] at hxy hyx hends
    change NoInterleave u.val v.val y.val (M.partner y).val at hc
    unfold NoInterleave at hc
    omega
  by_cases hxv : x = v
  · subst x
    rw [hrv] at hyx hends
    by_cases hyu : y = u
    · subst y; exact (lt_irrefl _) hyx
    by_cases hyv : y = v
    · subst y; exact (lt_irrefl _) hxy
    rw [hrt y hyu hyv] at hends
    have hc := reconnected_arc_no_interleave M j (hn_from_v hxa) y hya hyb hyu hyv
    change NoInterleave u.val v.val y.val (M.partner y).val at hc
    unfold NoInterleave at hc
    simp only [Fin.lt_def] at hxy hyx hends
    omega
  rw [hrt x hxu hxv] at hyx hends
  by_cases hyu : y = u
  · subst y
    rw [hru] at hends
    have hc := reconnected_arc_no_interleave M j (hn_from_u hyb) x hxa hxb hxu hxv
    change NoInterleave u.val v.val x.val (M.partner x).val at hc
    unfold NoInterleave at hc
    simp only [Fin.lt_def] at hxy hyx hends
    omega
  by_cases hyv : y = v
  · subst y
    rw [hrv] at hends
    have hc := reconnected_arc_no_interleave M j (hn_from_v hya) x hxa hxb hxu hxv
    change NoInterleave u.val v.val x.val (M.partner x).val at hc
    unfold NoInterleave at hc
    simp only [Fin.lt_def] at hxy hyx hends
    omega
  rw [hrt y hyu hyv] at hends
  exact M.noncrossing x y hxy hyx hends

/-- Actual arbitrary-size adjacent surgery, including m=0 and both end gaps. -/
def capSurgery : NCMatching m where
  partner := capPartner M j
  involutive := capPartner_involutive M j
  noFixed := capPartner_noFixed M j
  noncrossing x y hxy hyx hends := by
    apply reconnect_noncrossing M j (skipPair j x) (skipPair j y)
      (skipPair_survives j x).1 (skipPair_survives j x).2
      (skipPair_survives j y).1 (skipPair_survives j y).2
      (skipPair_strictMono j hxy)
    · simpa only [← skipPair_capPartner] using skipPair_strictMono j hyx
    · simpa only [← skipPair_capPartner] using skipPair_strictMono j hends

theorem capSurgery_reconnect (k : Fin m) :
    skipPair j ((capSurgery M j).partner k) = reconnectPartner M j (skipPair j k) :=
  skipPair_capPartner M j k
end Surgery
end CupCapBridgeProposal
