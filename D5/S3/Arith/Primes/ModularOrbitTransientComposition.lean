/- GID: D5/S3/Arith/Primes/ModularOrbitTransientComposition
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/ModularOrbitTransientComposition
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Compose exact modular transient kernels by maximum and lcm and count their complete finite orbit images. -/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.ModularOrbitTransientComposition

/-- An exact orbit rule comprises the modulus, transient length, and eventual
period. Exactness refers to each pair of distinct indices, not merely returns. -/
structure OrbitRule where
  modulus : ℕ
  transient : ℕ
  period : ℕ

def OrbitRule.Exact (r : OrbitRule) (f : ℕ → ℤ) : Prop :=
  ∀ n m, m < n →
    (f n ≡ f m [ZMOD (r.modulus:ℤ)] ↔ r.transient ≤ m ∧ r.period ∣ n-m)

def OrbitRule.combine (r s : OrbitRule) : OrbitRule :=
  ⟨r.modulus.lcm s.modulus, max r.transient s.transient, r.period.lcm s.period⟩

def trivial : OrbitRule := ⟨1, 0, 1⟩

/-- Composition requires no coprimality: both the modulus and return periods
combine by lcm, and the two transients combine by maximum. -/
theorem exact_combine (r s : OrbitRule) (f : ℕ → ℤ)
    (hr : r.Exact f) (hs : s.Exact f) : (r.combine s).Exact f := by
  intro n m hmn
  change (f n ≡ f m [ZMOD ((r.modulus.lcm s.modulus:ℕ):ℤ)]) ↔ _
  have hcast := Int.modEq_and_modEq_iff_modEq_lcm
    (a := f n) (b := f m) (m := (r.modulus:ℤ)) (n := (s.modulus:ℤ))
  rw [Int.lcm_natCast_natCast] at hcast
  rw [← hcast]
  have hrs := hr n m hmn
  have hss := hs n m hmn
  rw [hrs, hss]
  change (_ ∧ _) ∧ (_ ∧ _) ↔ max r.transient s.transient ≤ m ∧
    r.period.lcm s.period ∣ n-m
  rw [max_le_iff, Nat.lcm_dvd_iff]
  tauto

private theorem trivial_exact (f : ℕ → ℤ) : trivial.Exact f := by
  intro n m _
  simp [trivial, Int.ModEq]

/-- The combined rule over the empty list is exactly the modulus-one case. -/
def combined : List OrbitRule → OrbitRule
  | [] => trivial
  | r::rs => r.combine (combined rs)

theorem exact_combined (rs : List OrbitRule) (f : ℕ → ℤ)
    (h : ∀ r ∈ rs, r.Exact f) : (combined rs).Exact f := by
  induction rs with
  | nil => exact trivial_exact f
  | cons r rs ih =>
    exact exact_combine r (combined rs) f (h r (by simp))
      (ih (fun s hs => h s (List.mem_cons_of_mem _ hs)))

/-- A pairwise coprime list of moduli composes to their product. -/
theorem combined_modulus_eq_prod (rs : List OrbitRule)
    (h : rs.Pairwise (fun r s => r.modulus.Coprime s.modulus)) :
    (combined rs).modulus = (rs.map OrbitRule.modulus).prod := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have htail := List.Pairwise.of_cons h
    have hcop : r.modulus.Coprime ((rs.map OrbitRule.modulus).prod) := by
      rw [Nat.coprime_list_prod_right_iff]
      intro m hm
      obtain ⟨s, hs, hsm⟩ := List.mem_map.mp hm
      rw [← hsm]
      exact (List.pairwise_cons.mp h).1 s hs
    change r.modulus.lcm (combined rs).modulus = _
    rw [ih htail, hcop.lcm_eq_mul]
    rfl

theorem combined_period_positive (rs : List OrbitRule) (h : ∀ r ∈ rs, 0 < r.period) :
    0 < (combined rs).period := by
  induction rs with
  | nil => decide
  | cons r rs ih =>
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (h r (by simp)).ne'
      (ih (fun s hs => h s (List.mem_cons_of_mem _ hs))).ne')

/-- CRT composition for the ordinary product of pairwise coprime factors. -/
theorem exact_product_sequence (rs : List OrbitRule) (f : ℕ → ℤ)
    (hcop : rs.Pairwise (fun r s => r.modulus.Coprime s.modulus))
    (h : ∀ r ∈ rs, r.Exact f) (n m : ℕ) (hmn : m < n) :
    (f n ≡ f m [ZMOD (((rs.map OrbitRule.modulus).prod : ℕ):ℤ)]) ↔
      (combined rs).transient ≤ m ∧ (combined rs).period ∣ n-m := by
  exact (combined_modulus_eq_prod rs hcop) ▸ exact_combined rs f h n m hmn

/-- For a nonzero claimed period, a shift preserves all readings from k
onwards exactly when k is beyond the transient and the shift is a multiple
of the claimed period. Both thresholds are therefore sharp. -/
theorem exact_tail_period (r : OrbitRule) (f : ℕ → ℤ) (h : r.Exact f)
    (k l : ℕ) (hl : 0 < l) :
    (∀ n, k ≤ n → f (n+l) ≡ f n [ZMOD (r.modulus:ℤ)]) ↔
      r.transient ≤ k ∧ r.period ∣ l := by
  constructor
  · intro hp
    have hc := (h (k+l) k (by omega)).mp (hp k (Nat.le_refl _))
    simpa using hc
  · rintro ⟨hk, hd⟩ n hn
    apply (h (n+l) n (by omega)).mpr
    exact ⟨hk.trans hn, by simpa using hd⟩

/-- The prefix of size transient plus period contains no repeated residue. -/
theorem exact_prefix_injective (r : OrbitRule) (f : ℕ → ℤ) (h : r.Exact f) :
    Function.Injective fun n : Fin (r.transient+r.period) => f n % (r.modulus:ℤ) := by
  intro n m he
  have hless (n m : Fin (r.transient+r.period)) (hmn : m.val < n.val)
      (he' : f n ≡ f m [ZMOD (r.modulus:ℤ)]) : False := by
    obtain ⟨ha, hd⟩ := (h n.val m.val hmn).mp he'
    have hn := n.isLt
    have hle := Nat.le_of_dvd (by omega : 0 < n.val-m.val) hd
    omega
  apply Fin.ext
  by_cases hmn : m.val < n.val
  · exact (hless n m hmn he).elim
  · by_cases hnm : n.val < m.val
    · exact (hless m n hnm he.symm).elim
    · omega

/-- Every reading is represented in the initial window consisting of the
entire transient and one period. -/
theorem exact_window_represents (r : OrbitRule) (f : ℕ → ℤ) (h : r.Exact f)
    (hpos : 0 < r.period) (n : ℕ) :
    ∃ j : Fin (r.transient+r.period), f j ≡ f n [ZMOD (r.modulus:ℤ)] := by
  by_cases hn : n < r.transient+r.period
  · exact ⟨⟨n,hn⟩, Int.ModEq.refl _⟩
  · let j := r.transient+(n-r.transient)%r.period
    have hjlt : j < r.transient+r.period :=
      Nat.add_lt_add_left (Nat.mod_lt _ hpos) _
    have hjn : j < n := by omega
    have hjge : r.transient ≤ j := Nat.le_add_right _ _
    have hc : r.period ∣ n-j := by
      have ht := Nat.div_add_mod (n-r.transient) r.period
      refine ⟨(n-r.transient)/r.period, ?_⟩
      dsimp [j]
      omega
    exact ⟨⟨j,hjlt⟩, ((h n j hjn).mpr ⟨hjge,hc⟩).symm⟩

/-- The exact kernel provides a bijection between the transient-plus-period
window and the full residue image. This is an exact residue count. -/
noncomputable def exact_residue_image_equiv (r : OrbitRule) (f : ℕ → ℤ) (h : r.Exact f)
    (hpos : 0 < r.period) :
    Fin (r.transient+r.period) ≃ {z : ℤ // ∃ n : ℕ, f n % (r.modulus:ℤ) = z} :=
  Equiv.ofBijective (fun n => ⟨f n % (r.modulus:ℤ), n.val, rfl⟩)
    ⟨fun _ _ he => exact_prefix_injective r f h (congrArg Subtype.val he),
      fun ⟨z, n, hn⟩ => by
        obtain ⟨j, hj⟩ := exact_window_represents r f h hpos n
        change f j % (r.modulus:ℤ) = f n % (r.modulus:ℤ) at hj
        exact ⟨j, Subtype.ext (hj.trans hn)⟩⟩

theorem exact_residue_count (r : OrbitRule) (f : ℕ → ℤ) (h : r.Exact f)
    (hpos : 0 < r.period) :
    Nat.card {z : ℤ // ∃ n : ℕ, f n % (r.modulus:ℤ) = z} = r.transient+r.period := by
  rw [← Nat.card_congr (exact_residue_image_equiv r f h hpos), Nat.card_fin]

end D5.S3.Arith.Primes.ModularOrbitTransientComposition
