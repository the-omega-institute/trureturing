/- GID: D5/S3/Quantum/Fermionic/BcGhostRelativePBW
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostRelativePBW
   mirror-E: none(waiver:relative-ghost-pbw)
   anchors: []
   utility: none
   digest: Relative bc ghost PBW coordinates on the original Fock carrier. -/

import D5.S3.Quantum.Fermionic.BcGhostFock

/-! Ordered relative ghost words on the original finite occupation carrier. -/

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open private annihilate_coefficient from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostRelativePBW
abbrev Fock := CountableOccupationFock.Fock
def down : Fock := c 1 vacuum
@[simp] private theorem down_eq : down = ket {1} := ghost_vacuum.2.2.1
def relative : Submodule ℂ Fock := LinearMap.ker (b 0)
def gword : List (Module.End ℂ Fock) → Module.End ℂ Fock | [] => 1 | a :: w => a * gword w
def bneg (r : ℕ) : Module.End ℂ Fock := b (-(r : ℤ))
def cneg (r : ℕ) : Module.End ℂ Fock := c (-(r : ℤ))
def positiveSet (S : Finset ℕ) : Prop := ∀ r ∈ S, 1 ≤ r
def allowed : Set (Finset ℕ) := {S | 3 ∉ S}
@[simp] private theorem bneg_one : bneg 1 = annihilate 1 := by
  simp [bneg, b]
private theorem bneg_succ (r : ℕ) (hr : 2 ≤ r) : bneg r = create (2 * (r - 2)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
  simp [bneg, b]
@[simp] private theorem cneg_eq (r : ℕ) : cneg r = create (2 * r + 3) := by
  simp [cneg, c]
  congr 1
  omega
private theorem cpos_one : c (1 : ℤ) = create 1 := by
  simp [c]
private theorem cpos_succ (r : ℕ) (hr : 2 ≤ r) : c (r : ℤ) = annihilate (2 * (r - 2)) := by
  have h := (mode_correspondence (r - 2)).2.1
  rw [show (r : ℤ) = ((r - 2 : ℕ) : ℤ) + 2 by omega, h]
private theorem bpos_eq (r : ℕ) : b (r : ℤ) = annihilate (2 * r + 3) := by
  have hr : ¬(r : ℤ) ≤ -2 := by omega
  simp [b, hr]
  congr 1
def asc (S : Finset ℕ) : List ℕ := S.sort (· ≤ ·)
def W (B C : Finset ℕ) : Fock :=
  gword ((asc B).map bneg ++ (asc C).map cneg) down

def occ (B C : Finset ℕ) : Finset ℕ :=
  (if 1 ∈ B then ∅ else {1}) ∪
    (B.filter (fun r => 2 ≤ r)).image (fun r => 2 * (r - 2)) ∪
    C.image (fun s => 2 * s + 3)

def signExponent (B C : Finset ℕ) : ℕ :=
  C.card + (B.filter (fun r => 3 ≤ r)).card +
    ((B ×ˢ C).filter (fun p => p.2 + 4 ≤ p.1)).card +
    (if 1 ∈ B ∧ 2 ∈ B then 1 else 0)

def sign (B C : Finset ℕ) : ℂ := (-1 : ℂ) ^ signExponent B C

def Wcoord (B C : Finset ℕ) : Fock := sign B C • ket (occ B C)
private theorem gword_append (xs ys : List (Module.End ℂ Fock)) : gword (xs ++ ys) = gword xs * gword ys := by
  induction xs with
  | nil => simp [gword]
  | cons x xs ih => simp [gword, ih, mul_assoc]
private theorem W_eq_bword_cword (B C : Finset ℕ) : W B C = gword ((asc B).map bneg) (gword ((asc C).map cneg) down) := by
  simp [W, gword_append]

def cOcc (xs : List ℕ) : Finset ℕ := {1} ∪ xs.toFinset.image (fun s => 2 * s + 3)
private theorem asc_sorted (S : Finset ℕ) : (asc S).Pairwise (· < ·) := by
  exact (Finset.sortedLT_sort S).pairwise
private theorem asc_nodup (S : Finset ℕ) : (asc S).Nodup := by
  exact (Finset.sort_nodup S (· ≤ ·))
private theorem cword_sorted : ∀ (xs : List ℕ), xs.Pairwise (· < ·) → xs.Nodup →
    gword (xs.map cneg) down = (-1 : ℂ) ^ xs.length • ket (cOcc xs)
  | [], _, _ => by simp [gword, cOcc, down_eq]
  | x :: xs, hsort, hnodup => by
      have htail := cword_sorted xs hsort.tail hnodup.tail
      have hxnot : x ∉ xs := (List.nodup_cons.mp hnodup).1
      change cneg x (gword (xs.map cneg) down) = _
      rw [htail, cneg_eq, map_smul, create_ket]
      have hx : 2 * x + 3 ∉ cOcc xs := by
        intro hx
        simp only [cOcc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hx
        rcases hx with hx | ⟨y, hy, he⟩
        · omega
        · have hxy : x < y := (List.pairwise_cons.mp hsort).1 y (by simpa using hy)
          omega
      rw [if_neg hx]
      have hcount : lowerCount (2 * x + 3) (cOcc xs) = 1 := by
        unfold lowerCount cOcc
        have heq :
            (({1} ∪ xs.toFinset.image (fun s => 2 * s + 3)).filter
              (fun j => j < 2 * x + 3)) = {1} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
          constructor
          · rintro ⟨hj, hlt⟩
            rcases hj with rfl | ⟨y, hy, rfl⟩
            · simp
            · have hxy : x < y := (List.pairwise_cons.mp hsort).1 y (by simpa using hy)
              exact False.elim (by omega)
          · intro hj
            have hj0 : j = 1 := by simpa using hj
            subst j
            exact ⟨Or.inl rfl, by omega⟩
        rw [heq]
        simp
      rw [show phase (2 * x + 3) (cOcc xs) = (-1 : ℂ) by
        simp [phase, hcount]]
      have hset : insert (2 * x + 3) (cOcc xs) = cOcc (x :: xs) := by
        simp [cOcc, hxnot]
      rw [hset, smul_smul, List.length_cons, pow_succ]
private theorem cword_asc (C : Finset ℕ) : gword ((asc C).map cneg) down = (-1 : ℂ) ^ C.card • ket (cOcc (asc C)) := by
  rw [cword_sorted (asc C) (asc_sorted C) (asc_nodup C)]
  simp [asc, cOcc]

def bSite (r : ℕ) : ℕ := 2 * (r - 2)

def bOcc (C : Finset ℕ) (xs : List ℕ) : Finset ℕ :=
  cOcc (asc C) ∪ xs.toFinset.image bSite

def bStepExponent (r : ℕ) (C : Finset ℕ) : ℕ :=
  (if 3 ≤ r then 1 else 0) + (C.filter (fun s => s + 4 ≤ r)).card
private theorem sum_ge_three (S : Finset ℕ) :
    S.sum (fun r => if 3 ≤ r then 1 else 0) = (S.filter (fun r => 3 ≤ r)).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert r S hr ih => simp [hr, ih]
private theorem sum_crossing (B C : Finset ℕ) : B.sum (fun r => (C.filter (fun s => s + 4 ≤ r)).card) =
      ((B ×ˢ C).filter (fun p => p.2 + 4 ≤ p.1)).card := by
  classical
  rw [Finset.card_filter]
  rw [Finset.sum_product]
  simp only [Finset.card_filter]
private theorem bword_sorted : ∀ (xs : List ℕ) (C : Finset ℕ), xs.Pairwise (· < ·) → xs.Nodup → (∀ r ∈ xs, 2 ≤ r) →
    gword (xs.map bneg) (ket (cOcc (asc C))) = (-1 : ℂ) ^ (xs.toFinset.sum (fun r => bStepExponent r C)) • ket (bOcc C xs)
  | [], C, _, _, _ => by simp [gword, bOcc] | x :: xs, C, hsort, hnodup, htwo => by
      have htail := bword_sorted xs C hsort.tail hnodup.tail
        (fun r hr => htwo r (by simp [hr]))
      have hxnot : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hx2 : 2 ≤ x := htwo x (by simp)
      change bneg x (gword (xs.map bneg) (ket (cOcc (asc C)))) = _
      rw [htail, bneg_succ x hx2, map_smul, create_ket]
      have heven : bSite x ∉ bOcc C xs := by
        intro hx
        simp only [bOcc, Finset.mem_union, Finset.mem_image] at hx
        rcases hx with hx | ⟨y, hy, he⟩
        · simp only [cOcc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hx
          rcases hx with hx | ⟨s, hs, hse⟩
          · simp [bSite] at hx
          · have hsC : s ∈ C := by simpa [asc] using hs
            simp [bSite] at hse
            omega
        · have hxy : x < y := (List.pairwise_cons.mp hsort).1 y (by simpa using hy)
          simp [bSite] at he
          have hy2 : 2 ≤ y := htwo y (List.mem_cons_of_mem x (by simpa using hy))
          omega
      have heven' : 2 * (x - 2) ∉ bOcc C xs := by simpa [bSite] using heven
      rw [if_neg heven']
      have hcount : lowerCount (bSite x) (bOcc C xs) = bStepExponent x C := by
        have heq : (bOcc C xs).filter (fun j => j < bSite x) =
            (if 3 ≤ x then {1} else ∅) ∪
              (C.filter (fun s => s + 4 ≤ x)).image (fun s => 2 * s + 3) := by
          ext j
          simp only [bOcc, cOcc, asc, Finset.sort_toFinset, Finset.mem_filter,
            Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
          by_cases hx3 : 3 ≤ x <;> simp only [hx3, ↓reduceIte, Finset.mem_singleton, Finset.notMem_empty, false_or]
          all_goals
            constructor
            · rintro ⟨(hj | ⟨t, ht, he⟩) | ⟨y, hy, he⟩, hlt⟩
              · subst j
                simp_all [bSite] <;> omega
              · subst j
                simp only [bSite] at hlt
                first | exact Or.inr ⟨t, ⟨ht, by omega⟩, rfl⟩ |
                  exact ⟨t, ⟨ht, by omega⟩, rfl⟩
              · have hxy : x < y := (List.pairwise_cons.mp hsort).1 y
                  (by simpa using hy)
                simp only [bSite] at he hlt
                omega
            · intro hj
              first
              | rcases hj with rfl | ⟨t, ⟨ht, htx⟩, rfl⟩
                · exact ⟨Or.inl (Or.inl rfl), by simp [bSite]; omega⟩
                · exact ⟨Or.inl (Or.inr ⟨t, ht, rfl⟩), by simp [bSite]; omega⟩
              | rcases hj with ⟨t, ⟨ht, htx⟩, rfl⟩
                exact ⟨Or.inl (Or.inr ⟨t, ht, rfl⟩), by simp [bSite]; omega⟩
        have hd : Disjoint (if 3 ≤ x then ({1} : Finset ℕ) else ∅)
            ((C.filter (fun s => s + 4 ≤ x)).image (fun s => 2 * s + 3)) := by
          apply Finset.disjoint_left.mpr
          intro j hj hk
          split_ifs at hj with hx3
          · have hj1 : j = 1 := Finset.mem_singleton.mp hj
            obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hk
            omega
          · exact Finset.notMem_empty j hj
        unfold lowerCount bStepExponent
        rw [heq, Finset.card_union_of_disjoint hd,
          Finset.card_image_of_injective _ (by intro a b h; change 2 * a + 3 = 2 * b + 3 at h; omega)]
        split_ifs <;> simp
      have hp : phase (2 * (x - 2)) (bOcc C xs) =
          (-1 : ℂ) ^ bStepExponent x C := by
        change (-1 : ℂ) ^ lowerCount (bSite x) (bOcc C xs) = _
        rw [hcount]
      rw [hp]
      have hset : insert (2 * (x - 2)) (bOcc C xs) = bOcc C (x :: xs) := by
        simp [bOcc, bSite, Finset.union_insert, Finset.insert_union]
      rw [hset, smul_smul, ← pow_add]
      congr 2
      simp only [List.toFinset_cons]
      rw [Finset.sum_insert (by simpa using hxnot)]
      omega
private theorem bword_asc (B C : Finset ℕ) (hB : positiveSet B) (h1 : 1 ∉ B) :
    gword ((asc B).map bneg) (ket (cOcc (asc C))) = (-1 : ℂ) ^ ((B.filter (fun r => 3 ≤ r)).card +
        ((B ×ˢ C).filter (fun p => p.2 + 4 ≤ p.1)).card) • ket (cOcc (asc C) ∪ (B.image bSite)) := by
  have htwo : ∀ r ∈ asc B, 2 ≤ r := by
    intro r hr
    have hrB : r ∈ B := by simpa [asc] using hr
    have hrpos : 1 ≤ r := hB r hrB
    have hrne : r ≠ 1 := by
      intro he
      exact h1 (he ▸ hrB)
    omega
  rw [bword_sorted (asc B) C (asc_sorted B) (asc_nodup B) htwo]
  congr 1
  · have hsort : (asc B).toFinset = B := by
      exact Finset.sort_toFinset _ _
    rw [hsort]
    simp only [bStepExponent, Finset.sum_add_distrib]
    rw [sum_ge_three, sum_crossing]
  · simp [bOcc, asc]
private theorem asc_insert_one (B : Finset ℕ) (hB : 1 ∉ B) (hPos : positiveSet B) : asc (insert 1 B) = 1 :: asc B := by
  unfold asc
  apply Finset.sort_insert
  · intro r hr
    have hrpos := hPos r hr
    omega
  · exact hB
private theorem W_is_Wcoord (B C : Finset ℕ) (hBpos : positiveSet B) (hCpos : positiveSet C) : W B C = Wcoord B C := by
  classical
  have hzeroB : 0 ∉ B := by
    intro h
    exact Nat.not_succ_le_zero 0 (hBpos 0 h)
  have hzeroC : 0 ∉ C := by
    intro h
    exact Nat.not_succ_le_zero 0 (hCpos 0 h)
  rw [W_eq_bword_cword, cword_asc]
  by_cases hB : 1 ∈ B
  · rw [show B = insert 1 (B.erase 1) by exact (Finset.insert_erase hB).symm,
      asc_insert_one (B.erase 1) (Finset.notMem_erase 1 B) (by
        intro r hr
        exact hBpos r (Finset.mem_of_mem_erase hr))]
    have hErasePos : positiveSet (B.erase 1) := by
      intro r hr
      exact hBpos r (Finset.mem_of_mem_erase hr)
    change bneg 1 (gword ((asc (B.erase 1)).map bneg)
      ((-1 : ℂ) ^ C.card • ket (cOcc (asc C)))) = _
    rw [map_smul, bword_asc (B.erase 1) C hErasePos (Finset.notMem_erase 1 B)]
    rw [map_smul, bneg_one, map_smul, annihilate_ket]
    have hstate : 1 ∈ cOcc (asc C) ∪ (B.erase 1).image bSite := by
      simp [cOcc]
    rw [if_pos hstate]
    have hphase : phase 1 (cOcc (asc C) ∪ (B.erase 1).image bSite) =
        (-1 : ℂ) ^ (if 2 ∈ B then 1 else 0) := by
      have hfilter :
          (cOcc (asc C) ∪ (B.erase 1).image bSite).filter (fun j => j < 1) =
            if 2 ∈ B then {0} else ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
        constructor
        · rintro ⟨hj, hjlt⟩
          rcases hj with hj | ⟨r, hr, rfl⟩
          · simp only [cOcc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hj
            rcases hj with hj | ⟨s, hs, rfl⟩ <;> omega
          · have hrB : r ∈ B := Finset.mem_of_mem_erase hr
            have hrne : r ≠ 1 := by
              intro h
              subst r
              exact Finset.notMem_erase 1 B hr
            have hr2 : r = 2 := by
              have hrpos := hBpos r hrB
              unfold bSite at hjlt
              omega
            subst r
            simp [bSite, hrB]
        · intro hj
          by_cases h2 : 2 ∈ B
          · have hj0 : j = 0 := by simpa [h2] using hj
            subst j
            constructor
            · exact Or.inr ⟨2, Finset.mem_erase.mpr ⟨by omega, h2⟩, by simp [bSite]⟩
            · simp [bSite]
          · simp [h2] at hj
      unfold phase lowerCount
      rw [hfilter]
      by_cases h2 : 2 ∈ B <;> simp [h2]
    rw [hphase, smul_smul]
    have hset : (cOcc (asc C) ∪ (B.erase 1).image bSite).erase 1 = occ B C := by
      ext j
      simp only [cOcc, asc, Finset.sort_toFinset, occ, hB, ↓reduceIte,
        Finset.empty_union, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨hne, hj | hj⟩
        · rcases hj with hj | hj
          · exact (hne hj).elim
          · exact Or.inr hj
        · obtain ⟨r, ⟨hr1, hrB⟩, he⟩ := hj
          have hr2 : 2 ≤ r := by have := hBpos r hrB; omega
          exact Or.inl ⟨r, ⟨hrB, hr2⟩, he⟩
      · intro hj
        rcases hj with ⟨r, ⟨hrB, hr2⟩, he⟩ | ⟨t, ht, he⟩
        · have hne : j ≠ 1 := by omega
          exact ⟨hne, Or.inr ⟨r, ⟨by omega, hrB⟩, he⟩⟩
        · exact ⟨by omega, Or.inl (Or.inr ⟨t, ht, he⟩)⟩
    rw [hset]
    have hf : (B.erase 1).filter (fun r => 3 ≤ r) = B.filter (fun r => 3 ≤ r) := by
      rw [Finset.filter_erase]
      apply Finset.erase_eq_self.mpr
      simp
    have hx : ((B.erase 1 ×ˢ C).filter (fun p => p.2 + 4 ≤ p.1)) =
        ((B ×ˢ C).filter (fun p => p.2 + 4 ≤ p.1)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_erase]
      have hne : p.2 + 4 ≤ p.1 → p.1 ≠ 1 := by omega
      tauto
    rw [Finset.insert_erase hB]
    simp only [Wcoord, sign, signExponent, hf, hx, hB, true_and]
    simp only [pow_add, smul_smul, mul_assoc]
  · change gword ((asc B).map bneg)
      ((-1 : ℂ) ^ C.card • ket (cOcc (asc C))) = _
    rw [map_smul, bword_asc B C hBpos hB]
    have hf : B.filter (fun r => 2 ≤ r) = B := by
      apply Finset.filter_eq_self.mpr
      intro r hr
      have := hBpos r hr
      have : r ≠ 1 := by intro he; exact hB (he ▸ hr)
      omega
    have hset : cOcc (asc C) ∪ B.image bSite = occ B C := by
      change cOcc (asc C) ∪ B.image (fun r => 2 * (r - 2)) = occ B C
      simp [occ, hB, hf, cOcc, asc, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
    rw [hset]
    simp [Wcoord, sign, signExponent, hB, pow_add, smul_smul, mul_assoc]
private theorem mem_occ (j : ℕ) (B C : Finset ℕ) : j ∈ occ B C ↔ (j = 1 ∧ 1 ∉ B) ∨
      (∃ r ∈ B, 2 ≤ r ∧ bSite r = j) ∨ (∃ s ∈ C, 2 * s + 3 = j) := by
  classical
  by_cases h : 1 ∈ B <;>
    simp [occ, h, bSite, and_assoc, or_assoc]
private theorem occ_one (B C : Finset ℕ) : 1 ∈ occ B C ↔ 1 ∉ B := by
  rw [mem_occ]
  constructor
  · rintro (h | ⟨r, hr, hr2, he⟩ | ⟨s, hs, he⟩)
    · exact h.2
    · simp only [bSite] at he
      omega
    · omega
  · exact fun h => Or.inl ⟨rfl, h⟩
private theorem occ_bSite_mem (r : ℕ) (B C : Finset ℕ) (hr : 2 ≤ r) : bSite r ∈ occ B C ↔ r ∈ B := by
  rw [mem_occ]
  constructor
  · rintro (⟨he, _⟩ | ⟨t, ht, ht2, he⟩ | ⟨s, hs, he⟩)
    · simp only [bSite] at he
      omega
    · have : t = r := by dsimp only [bSite] at he; omega
      exact this ▸ ht
    · simp only [bSite] at he
      omega
  · intro h
    exact Or.inr (Or.inl ⟨r, h, hr, rfl⟩)
private theorem occ_cSite_mem (r : ℕ) (B C : Finset ℕ) : 2 * r + 3 ∈ occ B C ↔ r ∈ C := by
  rw [mem_occ]
  constructor
  · rintro (⟨he, _⟩ | ⟨t, ht, ht2, he⟩ | ⟨s, hs, he⟩)
    · omega
    · simp only [bSite] at he
      omega
    · have : s = r := by omega
      exact this ▸ hs
  · intro h
    exact Or.inr (Or.inr ⟨r, h, rfl⟩)

def invB (S : Finset ℕ) : Finset ℕ :=
  (if 1 ∉ S then {1} else ∅) ∪
    (S.filter (fun j => j % 2 = 0)).image (fun j => j / 2 + 2)

def invC (S : Finset ℕ) : Finset ℕ :=
  (S.filter (fun j => j % 2 = 1 ∧ 5 ≤ j)).image (fun j => j / 2 - 1)

def pairCarrier :=
  {p : Finset ℕ × Finset ℕ // positiveSet p.1 ∧ positiveSet p.2}

def pairToOcc (p : pairCarrier) : Finset ℕ := occ p.1.1 p.1.2

abbrev occupationCarrier := allowed

def pairToOccupation (p : pairCarrier) : occupationCarrier :=
  ⟨pairToOcc p, by
    change 3 ∉ occ p.1.1 p.1.2
    rw [mem_occ]
    rintro (⟨h, _⟩ | ⟨r, hr, hr2, he⟩ | ⟨s, hs, he⟩)
    · omega
    · simp only [bSite] at he
      omega
    · have := p.2.2 s hs
      omega⟩

def occToPair (S : Finset ℕ) : pairCarrier :=
  ⟨(invB S, invC S), by
    constructor
    · intro r hr
      simp only [invB, Finset.mem_union] at hr
      rcases hr with hr | hr
      · by_cases hS : 1 ∉ S
        · simp [hS] at hr
          omega
        · simp [hS] at hr
      · rcases Finset.mem_image.mp hr with ⟨j, hj, rfl⟩
        have hjcond := (Finset.mem_filter.mp hj).2
        omega
    · intro r hr
      simp only [invC, Finset.mem_image] at hr
      rcases hr with ⟨j, hj, rfl⟩
      have hjcond := (Finset.mem_filter.mp hj).2
      omega⟩
private theorem mem_invB (r : ℕ) (S : Finset ℕ) : r ∈ invB S ↔ (r = 1 ∧ 1 ∉ S) ∨ (2 ≤ r ∧ bSite r ∈ S) := by
  classical
  simp only [invB, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  have hh : (r ∈ if 1 ∉ S then ({1} : Finset ℕ) else ∅) ↔ r = 1 ∧ 1 ∉ S := by
    by_cases h : 1 ∉ S <;> simp [h]
  rw [hh]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j, ⟨hj, heven⟩, he⟩
    have hr : 2 ≤ r := by omega
    have hjr : j = bSite r := by simp only [bSite]; omega
    exact ⟨hr, hjr ▸ hj⟩
  · rintro ⟨hr, hj⟩
    exact ⟨bSite r, ⟨hj, by simp [bSite]⟩, by simp only [bSite]; omega⟩
private theorem mem_invC (r : ℕ) (S : Finset ℕ) : r ∈ invC S ↔ 1 ≤ r ∧ 2 * r + 3 ∈ S := by
  classical
  simp only [invC, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨j, ⟨hj, hodd, hj5⟩, he⟩
    have hr : 1 ≤ r := by omega
    have hjr : j = 2 * r + 3 := by omega
    exact ⟨hr, hjr ▸ hj⟩
  · rintro ⟨hr, hj⟩
    exact ⟨2 * r + 3, ⟨hj, by omega, by omega⟩, by omega⟩
private theorem invB_occ (B C : Finset ℕ) (hB : positiveSet B) : invB (occ B C) = B := by
  ext r
  rw [mem_invB, occ_one]
  by_cases hr : 2 ≤ r
  · rw [occ_bSite_mem r B C hr]
    simp only [hr, true_and]
    constructor
    · rintro (⟨he, _⟩ | h)
      · omega
      · exact h
    · exact Or.inr
  · constructor
    · rintro (⟨rfl, h⟩ | ⟨h, _⟩)
      · exact not_not.mp h
      · contradiction
    · intro h
      have hp := hB r h
      have he : r = 1 := by omega
      subst r
      exact Or.inl ⟨rfl, by simpa using h⟩
private theorem invC_occ (B C : Finset ℕ) (hC : positiveSet C) : invC (occ B C) = C := by
  ext r
  rw [mem_invC, occ_cSite_mem]
  exact ⟨And.right, fun h => ⟨hC r h, h⟩⟩
private theorem occ_inv (S : Finset ℕ) (h3 : 3 ∉ S) : occ (invB S) (invC S) = S := by
  ext j
  rw [mem_occ]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨r, hr, hr2, he⟩ | ⟨r, hr, he⟩)
    · by_contra hs
      exact h ((mem_invB 1 S).mpr (Or.inl ⟨rfl, hs⟩))
    · rcases (mem_invB r S).mp hr with ⟨h, _⟩ | ⟨_, h⟩
      · omega
      · exact he ▸ h
    · exact he ▸ ((mem_invC r S).mp hr).2
  · intro hj
    by_cases hj1 : j = 1
    · subst j
      exact Or.inl ⟨rfl, by simpa [mem_invB] using hj⟩
    · by_cases he : j % 2 = 0
      · refine Or.inr (Or.inl ⟨j / 2 + 2, ?_, by omega, ?_⟩)
        · rw [mem_invB]
          right
          exact ⟨by omega, by convert hj using 1 <;> simp only [bSite] <;> omega⟩
        · simp only [bSite]
          omega
      · have hjodd : j % 2 = 1 := by omega
        have hj5 : 5 ≤ j := by
          have hj3 : j ≠ 3 := by intro h; exact h3 (h ▸ hj)
          omega
        refine Or.inr (Or.inr ⟨j / 2 - 1, ?_, by omega⟩)
        rw [mem_invC]
        exact ⟨by omega, by convert hj using 1 <;> omega⟩

def pairOccupationEquiv : pairCarrier ≃ occupationCarrier where
  toFun := pairToOccupation
  invFun := fun S => occToPair S.1
  left_inv := by
    intro p
    apply Subtype.ext
    change (invB (occ p.1.1 p.1.2), invC (occ p.1.1 p.1.2)) = p.1
    rw [invB_occ p.1.1 p.1.2 (Subtype.prop p).1, invC_occ p.1.1 p.1.2 (Subtype.prop p).2]
  right_inv := by
    intro S
    apply Subtype.ext
    change occ (invB S.1) (invC S.1) = S.1
    exact occ_inv S.1 S.2
private theorem W_mem_relative (B C : Finset ℕ) (hB : positiveSet B) (hC : positiveSet C) : W B C ∈ relative := by
  change b 0 (W B C) = 0
  rw [W_is_Wcoord B C hB hC]
  have h3 := (pairToOccupation ⟨(B, C), hB, hC⟩).2
  change 3 ∉ occ B C at h3
  simp [b, Wcoord, h3]

def Wrel (p : pairCarrier) : relative :=
  ⟨W p.1.1 p.1.2, W_mem_relative p.1.1 p.1.2 (Subtype.prop p).1 (Subtype.prop p).2⟩
private theorem relative_coeff_three (v : relative) {S : Finset ℕ} (hS : 3 ∈ S) : v.1 S = 0 := by
  have hb : annihilate 3 v.1 = 0 := by
    simpa [relative, b] using v.2
  have hz := annihilate_coefficient 3 v.1 S hS
  rw [hb] at hz
  have hphase : phase 3 S ≠ 0 := pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)
  exact (mul_eq_zero.mp (by simpa using hz)).resolve_left hphase
private theorem relative_support_no_three (v : relative) : ∀ S ∈ v.1.support, 3 ∉ S := by
  intro S hS h3
  exact (Finsupp.mem_support_iff.mp hS) (relative_coeff_three v h3)

def supportedAllowed : Submodule ℂ Fock := Finsupp.supported ℂ ℂ allowed
private theorem no_three_annihilate (v : Fock) (h : ∀ S ∈ v.support, 3 ∉ S) : annihilate 3 v = 0 := by
  classical
  rw [annihilate, Finsupp.lsum_apply]
  simp only [Finsupp.sum, LinearMap.smulRight_apply, LinearMap.id_apply]
  apply Finset.sum_eq_zero
  intro S hS
  by_cases h3 : 3 ∈ S
  · exact False.elim (h S hS h3)
  · simp [annihilate_ket, h3]
private theorem relative_eq_supportedAllowed : relative = supportedAllowed := by
  apply Submodule.ext
  intro v
  constructor
  · intro hv
    change v ∈ Finsupp.supported ℂ ℂ allowed
    rw [Finsupp.mem_supported]
    intro S hS
    exact relative_support_no_three ⟨v, hv⟩ S hS
  · intro hv
    change b 0 v = 0
    have hs : ∀ S ∈ v.support, 3 ∉ S := by
      change v ∈ Finsupp.supported ℂ ℂ allowed at hv
      rw [Finsupp.mem_supported] at hv
      intro S hS
      exact hv hS
    simpa [b] using no_three_annihilate v hs

def relativeSupportedEquiv : relative ≃ₗ[ℂ] supportedAllowed :=
  LinearEquiv.ofEq relative supportedAllowed relative_eq_supportedAllowed

def ketEquiv : (allowed →₀ ℂ) ≃ₗ[ℂ] relative :=
  (Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) allowed).symm ≪≫ₗ
    relativeSupportedEquiv.symm

def signMap : (pairCarrier →₀ ℂ) →ₗ[ℂ] (pairCarrier →₀ ℂ) :=
  Finsupp.lsum ℂ (fun p => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
    (sign p.1.1 p.1.2 • Finsupp.single p 1))
private theorem signMap_single (p : pairCarrier) (a : ℂ) :
    signMap (Finsupp.single p a) = sign p.1.1 p.1.2 • Finsupp.single p a := by
  simp [signMap, mul_comm]
private theorem signMap_involution : signMap.comp signMap = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro p a
  change signMap (signMap (Finsupp.single p a)) = Finsupp.single p a
  rw [signMap_single, map_smul, signMap_single, smul_smul]
  have hpow : ∀ n : ℕ, ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, ih, mul_assoc]
  rw [show sign p.1.1 p.1.2 * sign p.1.1 p.1.2 = 1 from
    hpow (signExponent p.1.1 p.1.2), one_smul]

def signEquiv : (pairCarrier →₀ ℂ) ≃ₗ[ℂ] (pairCarrier →₀ ℂ) :=
  LinearEquiv.ofBijective signMap ⟨
    (fun x y h => by
      calc
        x = signMap (signMap x) := by
          rw [← LinearMap.comp_apply, signMap_involution]
          rfl
        _ = signMap (signMap y) := congrArg signMap h
        _ = y := by
          rw [← LinearMap.comp_apply, signMap_involution]
          rfl), (fun y => ⟨signMap y, by
      rw [← LinearMap.comp_apply, signMap_involution]
      rfl⟩)⟩

def basisEquiv : (pairCarrier →₀ ℂ) ≃ₗ[ℂ] relative :=
  signEquiv ≪≫ₗ Finsupp.mapDomain.linearEquiv ℂ ℂ pairOccupationEquiv ≪≫ₗ ketEquiv
private theorem ketEquiv_single (S : occupationCarrier) : (ketEquiv (Finsupp.single S 1) : Fock) = ket S.1 := by
  change (relativeSupportedEquiv.symm
    ((Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) allowed).symm
      (Finsupp.single S 1)) : Fock) = _
  change (((Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) allowed).symm
    (Finsupp.single S 1)) : Fock) = _
  exact Finsupp.supportedEquivFinsupp_symm_single allowed S 1
private theorem basisEquiv_single (p : pairCarrier) : basisEquiv (Finsupp.single p 1) = Wrel p := by
  apply Subtype.ext
  change (ketEquiv ((Finsupp.mapDomain.linearEquiv ℂ ℂ pairOccupationEquiv)
    (signMap (Finsupp.single p 1))) : Fock) = W p.1.1 p.1.2
  rw [signMap_single, map_smul, map_smul]
  change sign p.1.1 p.1.2 • (ketEquiv
    (Finsupp.mapDomain pairOccupationEquiv (Finsupp.single p 1)) : Fock) = _
  rw [Finsupp.mapDomain_single, ketEquiv_single, W_is_Wcoord p.1.1 p.1.2 p.2.1 p.2.2]
  rfl

def bPrefix (r : ℕ) (B : Finset ℕ) : ℕ := (B.filter (fun t => t < r)).card

def cPrefix (r : ℕ) (C : Finset ℕ) : ℕ := (C.filter (fun t => t < r)).card

private theorem count_union (j : ℕ) (S T : Finset ℕ) (h : Disjoint S T) :
    lowerCount j (S ∪ T) = lowerCount j S + lowerCount j T := by
  unfold lowerCount
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
private theorem count_image (j : ℕ) (S : Finset ℕ) (f : ℕ → ℕ) (h : Set.InjOn f (S : Set ℕ)) :
    lowerCount j (S.image f) = (S.filter (fun t => f t < j)).card := by
  unfold lowerCount
  rw [Finset.filter_image]
  apply Finset.card_image_iff.mpr
  exact h.mono (Finset.filter_subset _ _)
private theorem count_occ (j : ℕ) (B C : Finset ℕ) : lowerCount j (occ B C) = (if 1 ∉ B ∧ 1 < j then 1 else 0) +
      (B.filter (fun t => 2 ≤ t ∧ bSite t < j)).card + (C.filter (fun s => 2 * s + 3 < j)).card := by
  classical
  have h1 : Disjoint (if 1 ∈ B then (∅ : Finset ℕ) else {1})
      ((B.filter (fun t => 2 ≤ t)).image bSite) := by
    apply Finset.disjoint_left.mpr
    intro t ht hk
    split_ifs at ht with hB
    · exact Finset.notMem_empty t ht
    · have ht1 := Finset.mem_singleton.mp ht
      obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hk
      simp only [bSite] at he
      omega
  have h2 : Disjoint
      ((if 1 ∈ B then (∅ : Finset ℕ) else {1}) ∪
        (B.filter (fun t => 2 ≤ t)).image bSite)
      (C.image (fun s => 2 * s + 3)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hk
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_union.mp ht with ht | ht
    · split_ifs at ht with hB
      · exact Finset.notMem_empty t ht
      · have := Finset.mem_singleton.mp ht
        omega
    · obtain ⟨r, hr, he'⟩ := Finset.mem_image.mp ht
      simp only [bSite] at he'
      omega
  change lowerCount j (((if 1 ∈ B then ∅ else {1}) ∪
    (B.filter (fun t => 2 ≤ t)).image bSite) ∪ C.image (fun s => 2 * s + 3)) = _
  rw [count_union _ _ _ h2, count_union _ _ _ h1, count_image j _ bSite (by
      intro a ha b hb he
      have ha2 := (Finset.mem_filter.mp ha).2
      have hb2 := (Finset.mem_filter.mp hb).2
      simp only [bSite] at he
      omega), count_image j C (fun s => 2 * s + 3) (by
      intro a ha b hb he
      change 2 * a + 3 = 2 * b + 3 at he
      omega)]
  simp only [Finset.filter_filter]
  by_cases hB : 1 ∈ B <;> by_cases hj : 1 < j <;>
    simp [hB, hj, lowerCount, Finset.filter_singleton] <;> omega
private theorem cross_insert_b (r : ℕ) (B C : Finset ℕ) (h : r ∉ B) :
    ((insert r B ×ˢ C).filter (fun p => p.2 + 4 ≤ p.1)).card = ((B ×ˢ C).filter (fun p => p.2 + 4 ≤ p.1)).card +
        (C.filter (fun s => s + 4 ≤ r)).card := by
  rw [← sum_crossing, Finset.sum_insert h, sum_crossing]
  omega
private theorem cross_insert_c (r : ℕ) (B C : Finset ℕ) (h : r ∉ C) :
    ((B ×ˢ insert r C).filter (fun p => p.2 + 4 ≤ p.1)).card = ((B ×ˢ C).filter (fun p => p.2 + 4 ≤ p.1)).card +
        (B.filter (fun t => r + 4 ≤ t)).card := by
  simp only [Finset.card_filter, Finset.sum_product_right]
  rw [Finset.sum_insert h]
  omega
private theorem bprefix_split (r : ℕ) (B : Finset ℕ) (hr : 2 ≤ r) (hB : positiveSet B) :
    bPrefix r B = (if 1 ∈ B then 1 else 0) + (B.filter (fun t => 2 ≤ t ∧ t < r)).card := by
  classical
  have h1 : (if 1 ∈ B then 1 else 0) = ∑ t ∈ B, if t = 1 then 1 else 0 := by
    simp
  unfold bPrefix
  rw [h1, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hp := hB t ht
  by_cases ht1 : t = 1
  · subst t
    simp [show 1 < r by omega]
  · have ht2 : 2 ≤ t := by omega
    simp [ht1, ht2]
private theorem bcard_split (r : ℕ) (B : Finset ℕ) (hB : positiveSet B) : B.card = (if 1 ∈ B then 1 else 0) +
      (B.filter (fun t => 2 ≤ t ∧ t < r + 4)).card + (B.filter (fun t => r + 4 ≤ t)).card := by
  have hp := Finset.card_filter_add_card_filter_not (s := B) (p := fun t => t < r + 4)
  have hpre := bprefix_split (r + 4) B (by omega) hB
  have he : B.filter (fun t => ¬t < r + 4) = B.filter (fun t => r + 4 ≤ t) := by
    ext t
    simp
  rw [he] at hp
  unfold bPrefix at hpre
  omega
private theorem phase_sign_b (r : ℕ) (B C : Finset ℕ) (hr : 2 ≤ r) (hB : positiveSet B) (hnot : r ∉ B) :
    sign B C * phase (bSite r) (occ B C) = (-1 : ℂ) ^ bPrefix r B * sign (insert r B) C := by
  classical
  have hlow := count_occ (bSite r) B C
  have hfB : B.filter (fun t => 2 ≤ t ∧ bSite t < bSite r) =
      B.filter (fun t => 2 ≤ t ∧ t < r) := by
    apply Finset.filter_congr
    intro t ht
    dsimp only [bSite]
    omega
  have hfC : C.filter (fun s => 2 * s + 3 < bSite r) =
      C.filter (fun s => s + 4 ≤ r) := by
    apply Finset.filter_congr
    intro t ht
    dsimp only [bSite]
    omega
  rw [hfB, hfC] at hlow
  have hpre := bprefix_split r B hr hB
  have hf3 : ((insert r B).filter (fun t => 3 ≤ t)).card =
      (B.filter (fun t => 3 ≤ t)).card + (if 3 ≤ r then 1 else 0) := by
    by_cases h3 : 3 ≤ r <;> simp [Finset.filter_insert, h3, hnot]
  have hcross := cross_insert_b r B C hnot
  have hmod : (signExponent B C + lowerCount (bSite r) (occ B C)) % 2 =
      (bPrefix r B + signExponent (insert r B) C) % 2 := by
    rw [hlow, hpre]
    simp only [signExponent, hf3, hcross, Finset.mem_insert]
    by_cases hr2 : r = 2
    · subst r
      by_cases h1 : 1 ∈ B <;> simp [h1, hnot, bSite] <;> omega
    · have hr3 : 3 ≤ r := by omega
      have hn1 : 1 ≠ r := by omega
      have hn2 : 2 ≠ r := by omega
      have hb1 : 1 < bSite r := by dsimp only [bSite]; omega
      by_cases h1 : 1 ∈ B <;> by_cases h2 : 2 ∈ B <;>
        simp [h1, h2, hn1, hn2, hr3, hb1] <;> omega
  unfold sign phase
  rw [← pow_add, ← pow_add, neg_one_pow_eq_pow_mod_two (signExponent B C + lowerCount (bSite r) (occ B C)),
    neg_one_pow_eq_pow_mod_two (bPrefix r B + signExponent (insert r B) C), hmod]
private theorem phase_sign_c (r : ℕ) (B C : Finset ℕ) (hB : positiveSet B) (hnot : r ∉ C) :
    sign B C * phase (2 * r + 3) (occ B C) = (-1 : ℂ) ^ (B.card + cPrefix r C) * sign B (insert r C) := by
  classical
  have hlow := count_occ (2 * r + 3) B C
  have hfB : B.filter (fun t => 2 ≤ t ∧ bSite t < 2 * r + 3) =
      B.filter (fun t => 2 ≤ t ∧ t < r + 4) := by
    apply Finset.filter_congr
    intro t ht
    dsimp only [bSite]
    omega
  have hfC : C.filter (fun s => 2 * s + 3 < 2 * r + 3) =
      C.filter (fun s => s < r) := by
    apply Finset.filter_congr
    intro t ht
    omega
  rw [hfB, hfC] at hlow
  have hc := bcard_split r B hB
  have hcross := cross_insert_c r B C hnot
  have hmod : (signExponent B C + lowerCount (2 * r + 3) (occ B C)) % 2 =
      (B.card + cPrefix r C + signExponent B (insert r C)) % 2 := by
    rw [hlow, hc]
    simp only [signExponent, Finset.card_insert_of_notMem hnot, hcross, cPrefix]
    have hr1 : 1 < 2 * r + 3 := by omega
    by_cases h1 : 1 ∈ B <;> simp [h1, hr1] <;> omega
  unfold sign phase
  rw [← pow_add, ← pow_add, neg_one_pow_eq_pow_mod_two (signExponent B C + lowerCount (2 * r + 3) (occ B C)),
    neg_one_pow_eq_pow_mod_two (B.card + cPrefix r C + signExponent B (insert r C)), hmod]
private theorem phase_one (B C : Finset ℕ) : phase 1 (occ B C) = (-1 : ℂ) ^ (if 2 ∈ B then 1 else 0) := by
  have h := count_occ 1 B C
  have hb : B.filter (fun t => 2 ≤ t ∧ bSite t < 1) = B.filter (fun t => t = 2) := by
    apply Finset.filter_congr
    intro t ht
    dsimp only [bSite]
    omega
  have hc : C.filter (fun t => 2 * t + 3 < 1) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro t ht
    omega
  rw [hb, hc] at h
  by_cases h2 : 2 ∈ B <;> simp [phase, h, Finset.filter_eq', h2]
private theorem phase_sign_one (B C : Finset ℕ) (h : 1 ∉ B) : sign B C * phase 1 (occ B C) = sign (insert 1 B) C := by
  have hc := cross_insert_b 1 B C h
  have hz : C.filter (fun s => s + 4 ≤ 1) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs
    omega
  rw [hz] at hc
  simp only [Finset.card_empty, add_zero] at hc
  simp [sign, signExponent, phase_one, hc, h, Finset.filter_insert, pow_add]
private theorem occ_insert_b (r : ℕ) (B C : Finset ℕ) (hr : 2 ≤ r) : occ (insert r B) C = insert (bSite r) (occ B C) := by
  have hn : 1 ≠ r := by omega
  simp [occ, Finset.filter_insert, hr, hn, bSite, Finset.union_insert, Finset.insert_union]
private theorem occ_insert_one (B C : Finset ℕ) (h : 1 ∉ B) : occ (insert 1 B) C = (occ B C).erase 1 := by
  ext j
  simp only [Finset.mem_erase, mem_occ, Finset.mem_insert_self, not_true_eq_false, and_false, false_or]
  constructor
  · rintro (⟨r, hr, hr2, he⟩ | ⟨t, ht, he⟩)
    · rcases Finset.mem_insert.mp hr with rfl | hr
      · omega
      · have hn : j ≠ 1 := by dsimp only [bSite] at he; omega
        exact ⟨hn, Or.inr (Or.inl ⟨r, hr, hr2, he⟩)⟩
    · exact ⟨by omega, Or.inr (Or.inr ⟨t, ht, he⟩)⟩
  · rintro ⟨hn, ⟨he, _⟩ | ⟨r, hr, hr2, he⟩ | ⟨t, ht, he⟩⟩
    · exact (hn he).elim
    · exact Or.inl ⟨r, Finset.mem_insert_of_mem hr, hr2, he⟩
    · exact Or.inr ⟨t, ht, he⟩
private theorem occ_insert_c (r : ℕ) (B C : Finset ℕ) : occ B (insert r C) = insert (2 * r + 3) (occ B C) := by
  simp [occ, Finset.union_insert]
private theorem positive_insert (r : ℕ) (B : Finset ℕ) (hr : 1 ≤ r) (h : positiveSet B) : positiveSet (insert r B) := by
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact hr
  · exact h t ht
private theorem positive_erase (r : ℕ) (B : Finset ℕ) (h : positiveSet B) : positiveSet (B.erase r) :=
  fun t ht => h t (Finset.mem_of_mem_erase ht)
private theorem sign_square (n : ℕ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp
private theorem bneg_W (r : ℕ) (B C : Finset ℕ) (hrpos : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) : bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C := by
  classical
  rw [W_is_Wcoord B C hB hC]
  by_cases hmem : r ∈ B
  · rw [if_pos hmem]
    by_cases h1 : r = 1
    · subst r
      have hocc : 1 ∉ occ B C := by simpa only [occ_one, not_not] using hmem
      simp [Wcoord, bneg_one, hocc]
    · have hr2 : 2 ≤ r := by omega
      have hocc := (occ_bSite_mem r B C hr2).mpr hmem
      rw [show bneg r = create (bSite r) from bneg_succ r hr2]
      simp [Wcoord, hocc]
  · rw [if_neg hmem, W_is_Wcoord (insert r B) C (positive_insert r B hrpos hB) hC]
    by_cases h1 : r = 1
    · subst r
      have hocc : 1 ∈ occ B C := (occ_one B C).mpr hmem
      have hp : bPrefix 1 B = 0 := by
        unfold bPrefix
        rw [Finset.filter_eq_empty_iff.mpr (fun t ht => by have := hB t ht; omega)]
        rfl
      simp only [Wcoord, bneg_one, map_smul, annihilate_ket, if_pos hocc,
        smul_smul, hp, pow_zero, one_smul, ← occ_insert_one B C hmem]
      rw [phase_sign_one B C hmem, one_mul]
    · have hr2 : 2 ≤ r := by omega
      have hocc : bSite r ∉ occ B C := (occ_bSite_mem r B C hr2).not.mpr hmem
      simp only [Wcoord, bneg_succ r hr2, map_smul, create_ket]
      change sign B C • (if bSite r ∈ occ B C then 0 else
        phase (bSite r) (occ B C) • ket (insert (bSite r) (occ B C))) = _
      rw [if_neg hocc, smul_smul, phase_sign_b r B C hr2 hB hmem, occ_insert_b r B C hr2, smul_smul]
private theorem cpos_absent (r : ℕ) (B C : Finset ℕ) (hr : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) (h : r ∉ B) :
    c (r : ℤ) (W B C) = 0 := by
  rw [W_is_Wcoord B C hB hC]
  by_cases h1 : r = 1
  · subst r
    have ho : 1 ∈ occ B C := (occ_one B C).mpr h
    simp [Wcoord, cpos_one, ho]
  · have hr2 : 2 ≤ r := by omega
    have ho : bSite r ∉ occ B C := (occ_bSite_mem r B C hr2).not.mpr h
    rw [show c (r : ℤ) = annihilate (bSite r) from cpos_succ r hr2]
    simp [Wcoord, ho]
private theorem prefix_erase (r : ℕ) (B : Finset ℕ) : bPrefix r (B.erase r) = bPrefix r B := by
  simp [bPrefix, Finset.filter_erase]
private theorem cpos_W (r : ℕ) (B C : Finset ℕ) (hr : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) : c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0 := by
  classical
  by_cases hmem : r ∈ B
  · rw [if_pos hmem]
    have he := positive_erase r B hB
    have hz := cpos_absent r (B.erase r) C hr he hC (Finset.notMem_erase _ _)
    have hcar := LinearMap.congr_fun (ghost_mixed_car (-(r : ℤ)) (r : ℤ))
      (W (B.erase r) C)
    have hins := bneg_W r (B.erase r) C hr he hC
    simp only [Finset.notMem_erase, ↓reduceIte, Finset.insert_erase hmem, prefix_erase] at hins
    change b (-(r : ℤ)) (W (B.erase r) C) = _ at hins
    have hid : (-1 : ℂ) ^ bPrefix r B • c (r : ℤ) (W B C) = W (B.erase r) C := by
      simpa only [show -(r : ℤ) + (r : ℤ) = 0 by omega, ↓reduceIte,
        Module.End.mul_apply, LinearMap.add_apply, hz, map_zero, zero_add, hins, map_smul, Module.End.one_apply] using hcar
    calc
      c (r : ℤ) (W B C) = (-1 : ℂ) ^ bPrefix r B •
          ((-1 : ℂ) ^ bPrefix r B • c (r : ℤ) (W B C)) := by
        rw [smul_smul, sign_square, one_smul]
      _ = _ := congrArg (fun v : Fock => (-1 : ℂ) ^ bPrefix r B • v) hid
  · simp [hmem, cpos_absent r B C hr hB hC hmem]
private theorem cneg_W (r : ℕ) (B C : Finset ℕ) (hr : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) : cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C) := by
  classical
  rw [W_is_Wcoord B C hB hC]
  by_cases hmem : r ∈ C
  · have hocc := (occ_cSite_mem r B C).mpr hmem
    simp [Wcoord, cneg_eq, hmem, hocc]
  · rw [if_neg hmem, W_is_Wcoord B (insert r C) hB (positive_insert r C hr hC)]
    have hocc := (occ_cSite_mem r B C).not.mpr hmem
    simp only [Wcoord, cneg_eq, map_smul, create_ket, if_neg hocc, smul_smul, phase_sign_c r B C hB hmem, occ_insert_c]
private theorem bpos_absent (r : ℕ) (B C : Finset ℕ) (hB : positiveSet B) (hC : positiveSet C) (h : r ∉ C) :
    b (r : ℤ) (W B C) = 0 := by
  rw [W_is_Wcoord B C hB hC]
  have ho := (occ_cSite_mem r B C).not.mpr h
  simp [Wcoord, bpos_eq, ho]
private theorem bpos_W (r : ℕ) (B C : Finset ℕ) (hr : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) : b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0 := by
  classical
  by_cases hmem : r ∈ C
  · rw [if_pos hmem]
    have he := positive_erase r C hC
    have hz := bpos_absent r B (C.erase r) hB he (Finset.notMem_erase _ _)
    have hcar := LinearMap.congr_fun (ghost_mixed_car (r : ℤ) (-(r : ℤ)))
      (W B (C.erase r))
    have hins := cneg_W r B (C.erase r) hr hB he
    have hp : cPrefix r (C.erase r) = cPrefix r C := prefix_erase r C
    simp only [Finset.notMem_erase, ↓reduceIte, Finset.insert_erase hmem, hp] at hins
    change c (-(r : ℤ)) (W B (C.erase r)) = _ at hins
    have hid : (-1 : ℂ) ^ (B.card + cPrefix r C) • b (r : ℤ) (W B C) =
        W B (C.erase r) := by
      simpa only [show (r : ℤ) + -(r : ℤ) = 0 by omega, ↓reduceIte,
        Module.End.mul_apply, LinearMap.add_apply, hz, map_zero, add_zero, hins, map_smul, Module.End.one_apply] using hcar
    calc
      b (r : ℤ) (W B C) = (-1 : ℂ) ^ (B.card + cPrefix r C) •
          ((-1 : ℂ) ^ (B.card + cPrefix r C) • b (r : ℤ) (W B C)) := by
        rw [smul_smul, sign_square, one_smul]
      _ = _ := congrArg (fun v : Fock => (-1 : ℂ) ^ (B.card + cPrefix r C) • v) hid
  · simp [hmem, bpos_absent r B C hB hC hmem]
private theorem native_occupation_projections (r : ℕ) (B C : Finset ℕ)
    (hr : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) : bneg r (c (r : ℤ) (W B C)) = (if r ∈ B then W B C else 0) ∧
    cneg r (b (r : ℤ) (W B C)) = (if r ∈ C then W B C else 0) := by
  constructor
  · rw [cpos_W r B C hr hB hC]
    by_cases hm : r ∈ B
    · simp only [hm, ↓reduceIte, map_smul]
      rw [bneg_W r (B.erase r) C hr (positive_erase r B hB) hC]
      simp only [Finset.notMem_erase, ↓reduceIte, Finset.insert_erase hm, prefix_erase, smul_smul, sign_square, one_smul]
    · simp [hm]
  · rw [bpos_W r B C hr hB hC]
    by_cases hm : r ∈ C
    · simp only [hm, ↓reduceIte, map_smul]
      rw [cneg_W r B (C.erase r) hr hB (positive_erase r C hC)]
      have hp : cPrefix r (C.erase r) = cPrefix r C := prefix_erase r C
      simp only [Finset.notMem_erase, ↓reduceIte, Finset.insert_erase hm, hp, smul_smul, sign_square, one_smul]
    · simp [hm]
private theorem relative_pbw_mode_intertwining : (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      bneg r (W B C) = if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C)) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → bneg r (c (r : ℤ) (W B C)) =
      if r ∈ B then W B C else 0) ∧ (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      cneg r (b (r : ℤ) (W B C)) = if r ∈ C then W B C else 0) := by
  exact ⟨bneg_W, cpos_W, cneg_W, bpos_W, fun r B C hr hB hC => by
      simpa using (native_occupation_projections r B C hr hB hC).1, fun r B C hr hB hC => by
      simpa using (native_occupation_projections r B C hr hB hC).2⟩
private theorem relative_pbw_basis : (∀ p : pairCarrier, basisEquiv (Finsupp.single p 1) = Wrel p) ∧
    Function.Bijective basisEquiv := by
  exact ⟨basisEquiv_single, basisEquiv.bijective⟩
private theorem down_positive (r : ℕ) (hr : 1 ≤ r) : c (r : ℤ) down = 0 ∧ b (r : ℤ) down = 0 := by
  have he : positiveSet ∅ := by intro t ht; simp at ht
  have hw : W ∅ ∅ = down := by simp [W, asc, gword]
  constructor
  · simpa only [hw] using cpos_absent r ∅ ∅ hr he he (by simp)
  · simpa only [hw] using bpos_absent r ∅ ∅ he he (by simp)

theorem relative_pbw_complete : (∀ (B C : Finset ℕ), positiveSet B → positiveSet C → W B C = Wcoord B C) ∧
    (∀ p : pairCarrier, basisEquiv (Finsupp.single p 1) = Wrel p) ∧ Function.Bijective basisEquiv ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C)) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C → bneg r (c (r : ℤ) (W B C)) =
      if r ∈ B then W B C else 0) ∧ (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      cneg r (b (r : ℤ) (W B C)) = if r ∈ C then W B C else 0) ∧ (∀ (B C : Finset ℕ), positiveSet B → positiveSet C →
      invB (occ B C) = B ∧ invC (occ B C) = C) ∧ (∀ S : Finset ℕ, 3 ∉ S → occ (invB S) (invC S) = S) ∧
    (∀ r : ℕ, 1 ≤ r → c (r : ℤ) down = 0 ∧ b (r : ℤ) down = 0) := by
  rcases relative_pbw_basis with ⟨hunit, hbij⟩
  rcases relative_pbw_mode_intertwining with
    ⟨hbneg, hcpos, hcneg, hbpos, hprojB, hprojC⟩
  exact ⟨W_is_Wcoord, hunit, hbij, hbneg, hcpos, hcneg, hbpos, hprojB, hprojC,
    fun B C hB hC => ⟨invB_occ B C hB, invC_occ B C hC⟩, occ_inv, down_positive⟩

end D5.S3.Quantum.Fermionic.BcGhostRelativePBW
