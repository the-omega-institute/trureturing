/- GID: D5/S3/Quantum/Fermionic/BcGhostRelativePBW
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostRelativePBW
   mirror-E: none(waiver:relative-ghost-pbw)
   anchors: []
   utility: none
   digest: Actual relative bc ghost words and occupation coordinates on the original Fock carrier. -/

import D5.S3.Quantum.Fermionic.BcGhostFock

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

def gword : List (Module.End ℂ Fock) → Module.End ℂ Fock
  | [] => 1
  | a :: w => a * gword w

def bneg (r : ℕ) : Module.End ℂ Fock := b (-(r : ℤ))

def cneg (r : ℕ) : Module.End ℂ Fock := c (-(r : ℤ))

def positiveSet (S : Finset ℕ) : Prop := ∀ r ∈ S, 1 ≤ r

def allowed : Set (Finset ℕ) := {S | 3 ∉ S}

@[simp] private theorem bneg_one : bneg 1 = annihilate 1 := by
  simp [bneg, b]

private theorem bneg_succ (r : ℕ) (hr : 2 ≤ r) :
    bneg r = create (2 * (r - 2)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
  simp [bneg, b]

@[simp] private theorem cneg_eq (r : ℕ) : cneg r = create (2 * r + 3) := by
  simp [cneg, c]
  congr 1
  omega

private theorem cpos_one : c (1 : ℤ) = create 1 := by
  simp [c]

private theorem cpos_succ (r : ℕ) (hr : 2 ≤ r) :
    c (r : ℤ) = annihilate (2 * (r - 2)) := by
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
    ((B.product C).filter (fun p => p.2 + 4 ≤ p.1)).card +
    (if 1 ∈ B ∧ 2 ∈ B then 1 else 0)

def sign (B C : Finset ℕ) : ℂ := (-1 : ℂ) ^ signExponent B C

def Wcoord (B C : Finset ℕ) : Fock := sign B C • ket (occ B C)

private theorem gword_append (xs ys : List (Module.End ℂ Fock)) :
    gword (xs ++ ys) = gword xs * gword ys := by
  induction xs with
  | nil => simp [gword]
  | cons x xs ih => simp [gword, ih, mul_assoc]

private theorem W_eq_bword_cword (B C : Finset ℕ) :
    W B C = gword ((asc B).map bneg) (gword ((asc C).map cneg) down) := by
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
        · have hxy : x < y := (List.pairwise_cons.mp hsort).1 y hy
          omega
      rw [if_neg hx]
      have hcount : lowerCount (2 * x + 3) (cOcc xs) = 1 := by
        unfold lowerCount cOcc
        have heq :
            (({1} ∪ xs.toFinset.image (fun s => 2 * s + 3)).filter
              (fun j => j < 2 * x + 3)) = {1} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_image]
          constructor
          · rintro ⟨hj, hlt⟩
            rcases hj with rfl | ⟨y, hy, rfl⟩
            · simp
            · have hxy : x < y := (List.pairwise_cons.mp hsort).1 y hy
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

private theorem cword_asc (C : Finset ℕ) :
    gword ((asc C).map cneg) down = (-1 : ℂ) ^ C.card • ket (cOcc (asc C)) := by
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

private theorem sum_crossing (B C : Finset ℕ) :
    B.sum (fun r => (C.filter (fun s => s + 4 ≤ r)).card) =
      ((B.product C).filter (fun p => p.2 + 4 ≤ p.1)).card := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert r B hr ih =>
      rw [Finset.sum_insert hr, ih]
      have hdecomp :
          ((insert r B).product C).filter (fun p => p.2 + 4 ≤ p.1) =
            (Finset.map (Function.Embedding.sectR r ℕ)
                (C.filter (fun s => s + 4 ≤ r))) ∪
              ((B.product C).filter (fun p => p.2 + 4 ≤ p.1)) := by
        ext p
        rcases p with ⟨p, q⟩
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_map,
          Finset.mem_product, Function.Embedding.sectR_apply]
        constructor
        · rintro ⟨⟨hp, hq⟩, hlt⟩
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact Or.inl ⟨q, ⟨hq, hlt⟩, rfl⟩
          · exact Or.inr ⟨⟨hp, hq⟩, hlt⟩
        · rintro (⟨q, ⟨hq, hlt⟩, rfl⟩ | ⟨⟨hp, hq⟩, hlt⟩)
          · exact ⟨⟨Finset.mem_insert.mpr (Or.inl rfl), hq⟩, hlt⟩
          · exact ⟨⟨Finset.mem_insert.mpr (Or.inr hp), hq⟩, hlt⟩
      rw [hdecomp]
      rw [Finset.card_union_of_disjoint]
      · simp
      · rw [Finset.disjoint_left]
        intro p hp hq
        have hq' := Finset.mem_filter.mp hq |>.1
        exact hr (Finset.mem_product.mp hq').1

private theorem bword_sorted : ∀ (xs : List ℕ) (C : Finset ℕ),
    xs.Pairwise (· < ·) → xs.Nodup → (∀ r ∈ xs, 2 ≤ r) →
    gword (xs.map bneg) (ket (cOcc (asc C))) =
      (-1 : ℂ) ^ (xs.toFinset.sum (fun r => bStepExponent r C)) •
        ket (bOcc C xs)
  | [], C, _, _, _ => by simp [gword, bOcc]
  | x :: xs, C, hsort, hnodup, htwo => by
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
        · have hxy : x < y := (List.pairwise_cons.mp hsort).1 y hy
          simp [bSite] at he
          have hy2 : 2 ≤ y := htwo y (by simpa using hy)
          omega
      have heven' : 2 * (x - 2) ∉ bOcc C xs := by simpa [bSite] using heven
      rw [if_neg heven']
      have hcount : lowerCount (bSite x) (bOcc C xs) = bStepExponent x C := by
        unfold lowerCount bOcc bStepExponent bSite
        have heq :
            ((cOcc (asc C) ∪ xs.toFinset.image (fun r => 2 * (r - 2))).filter
              (fun j => j < 2 * (x - 2))) =
              ((if 3 ≤ x then {1} else ∅) ∪
                (C.filter (fun s => s + 4 ≤ x)).image (fun s => 2 * s + 3)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_image]
          constructor
          · rintro ⟨hj, hlt⟩
            rcases hj with hj | ⟨y, hy, rfl⟩
            · simp only [cOcc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hj
              rcases hj with hj | ⟨s, hs, rfl⟩
              · by_cases hx3 : 3 ≤ x
                · have hj1 : j = 1 := by simpa [hx3] using hj
                  subst j
                  exact ⟨Or.inl (Or.inl rfl), by omega⟩
                · simp [hx3] at hj
              · have hsC := (Finset.mem_filter.mp hs).1
                have hs4 := (Finset.mem_filter.mp hs).2
                by_cases hsAsc : s ∈ asc C
                · exact ⟨Or.inl (Or.inr ⟨s, hsAsc, rfl⟩), by omega⟩
                · have hsC' : s ∈ C := by simpa [asc] using hsC
                  exact False.elim (hsAsc (by simpa [asc] using hsC'))
            · have hxy : x < y := (List.pairwise_cons.mp hsort).1 y hy
              have hy2 : 2 ≤ y := htwo y hy
              simp [bSite] at hlt
              omega
          · intro hj
            rcases hj with hj | ⟨s, hs, rfl⟩
            · have hj1 : j = 1 := by simpa using hj
              subst j
              exact ⟨Or.inl (Or.inl rfl), by omega⟩
            · have hs4 := (Finset.mem_filter.mp hs).2
              exact ⟨Or.inl (Or.inr ⟨s, (Finset.mem_filter.mp hs).1, rfl⟩), by omega⟩
        rw [heq]
        simp [Finset.card_union_of_disjoint]
      rw [show phase (2 * (x - 2)) (bOcc C xs) = (-1 : ℂ) ^ bStepExponent x C by
        simp [phase, hcount]]
      have hset : insert (bSite x) (bOcc C xs) = bOcc C (x :: xs) := by
        simp [bOcc, bSite, hxnot]
      change _ • _ • ket (insert (bSite x) (bOcc C xs)) = _
      rw [hset, smul_smul, ← pow_add]
      congr 1
      simp [bStepExponent, Finset.sum_insert hxnot]

private theorem bword_asc (B C : Finset ℕ)
    (hB : positiveSet B) (h1 : 1 ∉ B) :
    gword ((asc B).map bneg) (ket (cOcc (asc C))) =
      (-1 : ℂ) ^ ((B.filter (fun r => 3 ≤ r)).card +
        ((B.product C).filter (fun p => p.2 + 4 ≤ p.1)).card) •
        ket (cOcc (asc C) ∪ (B.image bSite)) := by
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

private theorem asc_insert_one (B : Finset ℕ) (hB : 1 ∉ B) (hPos : positiveSet B) :
    asc (insert 1 B) = 1 :: asc B := by
  unfold asc
  apply Finset.sort_insert
  · intro r hr
    have hrpos := hPos r hr
    omega
  · exact hB

private theorem W_is_Wcoord (B C : Finset ℕ)
    (hBpos : positiveSet B) (hCpos : positiveSet C) : W B C = Wcoord B C := by
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
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image]
        constructor
        · rintro ⟨hj, hjlt⟩
          rcases hj with hj | ⟨r, hr, rfl⟩
          · simp only [cOcc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hj
            rcases hj with hj | ⟨s, hs, rfl⟩ <;> omega
          · have hrB : r ∈ B := Finset.mem_of_mem_erase hr
            have hrne : r ≠ 1 := by
              intro h; subst r
              exact Finset.notMem_erase 1 B hr
            have hr2 : r = 2 := by
              unfold bSite at hjlt
              omega
            subst r
            simp [hrB]
        · intro hj
          by_cases h2 : 2 ∈ B
          · have hj0 : j = 0 := by simpa [h2] using hj
            subst j
            constructor
            · exact ⟨Or.inr ⟨2, Finset.mem_erase.mpr ⟨by omega, h2⟩, by simp [bSite]⟩⟩
            · omega
          · simp [h2] at hj
      unfold phase lowerCount
      rw [hfilter]
      by_cases h2 : 2 ∈ B <;> simp [h2]
    rw [hphase, smul_smul]
    have hset : (cOcc (asc C) ∪ (B.erase 1).image bSite).erase 1 = occ B C := by
      ext j
      simp [occ, cOcc, Finset.mem_erase, bSite, asc]
      omega
    rw [hset]
    unfold Wcoord sign signExponent
    simp [hB]
  · change gword ((asc B).map bneg)
      ((-1 : ℂ) ^ C.card • ket (cOcc (asc C))) = _
    rw [map_smul, bword_asc B C hBpos hB]
    have hset : cOcc (asc C) ∪ B.image bSite =
        insert 1 ((B.filter (fun r => 2 ≤ r)).image bSite ∪ C.image (fun s => 2 * s + 3)) := by
      ext j
      simp [cOcc, asc, bSite, hB]
      omega
    rw [hset]
    unfold Wcoord sign signExponent occ
    simp [hB, hzeroB, hzeroC, pow_add, add_assoc, add_left_comm, add_comm]

private theorem occ_bSite_mem (r : ℕ) (B C : Finset ℕ) (hr : 2 ≤ r) :
    bSite r ∈ occ B C ↔ r ∈ B := by
  classical
  unfold occ bSite
  split <;> rename_i h1
  · simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      rcases h with h | h
      · rcases Finset.mem_image.mp h with ⟨s, hs, he⟩
        have hs2 := (Finset.mem_filter.mp hs).2
        omega
      · rcases Finset.mem_image.mp h with ⟨s, hs, he⟩
        omega
    · intro h
      exact Or.inl ⟨r, ⟨h, hr⟩, by simp [bSite]⟩
  · simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      rcases h with h | h
      · omega
      · rcases h with h | h
        · rcases Finset.mem_image.mp h with ⟨s, hs, he⟩
          have hs2 := (Finset.mem_filter.mp hs).2
          omega
        · rcases Finset.mem_image.mp h with ⟨s, hs, he⟩
          omega
    · intro h
      exact Or.inl (Or.inr ⟨r, ⟨h, hr⟩, by simp [bSite]⟩)

private theorem occ_cSite_mem (r : ℕ) (B C : Finset ℕ) :
    2 * r + 3 ∈ occ B C ↔ r ∈ C := by
  classical
  unfold occ
  split <;> rename_i h1
  · simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      rcases h with h | h
      · rcases Finset.mem_image.mp h with ⟨s, hs, he⟩
        have hs2 := (Finset.mem_filter.mp hs).2
        omega
      · rcases Finset.mem_image.mp h with ⟨s, hs, he⟩
        omega
    · intro h
      exact Or.inr ⟨r, h, by simp⟩
  · simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      rcases h with h | h
      · omega
      · rcases h with h | h
        · rcases Finset.mem_image.mp h with ⟨s, hs, he⟩
          have hs2 := (Finset.mem_filter.mp hs).2
          omega
        · rcases Finset.mem_image.mp h with ⟨s, hs, he⟩
          omega
    · intro h
      exact Or.inr (Or.inr ⟨r, h, by simp⟩)

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
    simp [occ]
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

private theorem invB_occ (B C : Finset ℕ) (hB : positiveSet B) :
    invB (occ B C) = B := by
  ext r
  by_cases hr1 : r = 1
  · subst r
    simp [invB, occ]
  · have hr2 : 2 ≤ r := by omega
    by_cases hrB : r ∈ B
    · have hsite : bSite r ∈ occ B C := by
        unfold bSite
        exact (occ_bSite_mem r B C hr2).2 hrB
      simp [invB, occ, hr1, hrB, hr2, hsite, bSite]
    · have hsite : bSite r ∉ occ B C := by
        unfold bSite
        exact (occ_bSite_mem r B C hr2).not.mpr hrB
      simp [invB, occ, hr1, hrB, hr2, hsite, bSite]

private theorem invC_occ (B C : Finset ℕ) (hC : positiveSet C) :
    invC (occ B C) = C := by
  ext s
  by_cases hs : s ∈ C
  · have hsite : 2 * s + 3 ∈ occ B C := (occ_cSite_mem s B C).2 hs
    simp [invC, occ, hs, hsite]
  · have hsite : 2 * s + 3 ∉ occ B C := (occ_cSite_mem s B C).not.mpr hs
    simp [invC, occ, hs, hsite]

private theorem occ_inv (S : Finset ℕ) (h3 : 3 ∉ S) : occ (invB S) (invC S) = S := by
  ext j
  simp [occ, invB, invC]
  omega

def pairOccupationEquiv : pairCarrier ≃ occupationCarrier where
  toFun := pairToOccupation
  invFun := fun S => occToPair S.1
  left_inv := by
    intro p
    apply Subtype.ext
    change (invB (occ p.1.1 p.1.2), invC (occ p.1.1 p.1.2)) = p.1
    rw [invB_occ p.1.1 p.1.2 (Subtype.prop p).1,
      invC_occ p.1.1 p.1.2 (Subtype.prop p).2]
  right_inv := by
    intro S
    apply Subtype.ext
    change occ (invB S.1) (invC S.1) = S.1
    exact occ_inv S.1 S.2

private theorem W_mem_relative (B C : Finset ℕ)
    (hB : positiveSet B) (hC : positiveSet C) : W B C ∈ relative := by
  change b 0 (W B C) = 0
  rw [W_is_Wcoord B C hB hC]
  simp [b, Wcoord, occ, sign]

def Wrel (p : pairCarrier) : relative :=
  ⟨W p.1.1 p.1.2,
    W_mem_relative p.1.1 p.1.2 (Subtype.prop p).1 (Subtype.prop p).2⟩

private theorem relative_coeff_three (v : relative) {S : Finset ℕ} (hS : 3 ∈ S) :
    v.1 S = 0 := by
  have hb : annihilate 3 v.1 = 0 := by
    simpa [relative, b] using v.2
  have hz := annihilate_coefficient 3 v.1 S hS
  rw [hb] at hz
  have hphase : phase 3 S ≠ 0 := pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)
  exact (mul_eq_zero.mp (by simpa using hz)).resolve_left hphase

private theorem relative_support_no_three (v : relative) :
    ∀ S ∈ v.1.support, 3 ∉ S := by
  intro S hS h3
  exact (Finsupp.mem_support_iff.mp hS) (relative_coeff_three v h3)

def supportedAllowed : Submodule ℂ Fock := Finsupp.supported ℂ ℂ allowed

private theorem no_three_annihilate (v : Fock)
    (h : ∀ S ∈ v.support, 3 ∉ S) : annihilate 3 v = 0 := by
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
    change ∀ S ∈ v.support, S ∈ allowed
    intro S hS
    exact relative_support_no_three ⟨v, hv⟩ S hS
  · intro hv
    change b 0 v = 0
    have hs : ∀ S ∈ v.support, 3 ∉ S := by
      change ∀ S ∈ v.support, S ∈ allowed at hv
      intro S hS
      exact hv S hS
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
  rw [signMap_single, map_smul, signMap_single]
  simp [sign, pow_add]

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
          rfl),
    (fun y => ⟨signMap y, by
      rw [← LinearMap.comp_apply, signMap_involution]
      rfl⟩)⟩

def basisEquiv : (pairCarrier →₀ ℂ) ≃ₗ[ℂ] relative :=
  signEquiv ≪≫ₗ Finsupp.mapDomain.linearEquiv ℂ ℂ pairOccupationEquiv ≪≫ₗ ketEquiv

private theorem basisEquiv_single (p : pairCarrier) :
    basisEquiv (Finsupp.single p 1) = Wrel p := by
  apply Subtype.ext
  rw [basisEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  simp [signEquiv, signMap, ketEquiv, Wrel,
    W_is_Wcoord p.1.1 p.1.2 (Subtype.prop p).1 (Subtype.prop p).2]

def bPrefix (r : ℕ) (B : Finset ℕ) : ℕ := (B.filter (fun t => t < r)).card

def cPrefix (r : ℕ) (C : Finset ℕ) : ℕ := (C.filter (fun t => t < r)).card

private theorem occ_one_mem (B C : Finset ℕ) (hB : 1 ∉ B) :
    1 ∉ occ B C := by
  unfold occ
  split <;> simp [hB]

private theorem bneg_W (r : ℕ) (B C : Finset ℕ)
    (hrpos : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) :
    bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C := by
  classical
  rw [W_is_Wcoord B C hB hC]
  unfold Wcoord
  by_cases hmem : r ∈ B
  · have hsign : sign B C ≠ 0 := pow_ne_zero _ (by norm_num)
    by_cases h1 : r = 1
    · subst r
      rw [bneg_one, map_smul, annihilate_ket]
      simp [Wcoord, occ, hmem, hsign]
    · have h2 : 2 ≤ r := by omega
      have hocc : bSite r ∈ occ B C := (occ_bSite_mem r B C h2).2 hmem
      have hocc' : 2 * (r - 2) ∈ occ B C := by simpa [bSite] using hocc
      rw [bneg_succ r h2, map_smul, create_ket, if_pos hocc']
      simp [Wcoord, occ, hmem, hsign]
  · by_cases h1 : r = 1
    · subst r
      have hocc : 1 ∉ occ B C := occ_one_mem B C hmem
      rw [bneg_one, map_smul, annihilate_ket, if_neg hocc]
      simp [Wcoord, occ, sign, signExponent, bPrefix, hmem]
    · have h2 : 2 ≤ r := by omega
      have hBins : positiveSet (insert r B) := by
        intro t ht
        simp only [Finset.mem_insert] at ht
        rcases ht with rfl | ht
        · exact hrpos
        · exact hB t ht
      rw [W_is_Wcoord (insert r B) C hBins hC]
      have hocc' : 2 * (r - 2) ∉ occ B C := by
        intro h
        apply hmem
        exact (occ_bSite_mem r B C h2).1 (by simpa [bSite] using h)
      rw [bneg_succ r h2, map_smul, create_ket, if_neg hocc']
      simp [Wcoord, occ, sign, signExponent, bPrefix, hmem, h1, h2, bSite, hocc']

private theorem cpos_W (r : ℕ) (B C : Finset ℕ)
    (hrpos : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) :
    c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0 := by
  classical
  rw [W_is_Wcoord B C hB hC]
  unfold Wcoord
  by_cases hmem : r ∈ B
  · have hBerase : positiveSet (B.erase r) := by
      intro t ht
      exact hB t (Finset.mem_of_mem_erase ht)
    rw [W_is_Wcoord (B.erase r) C hBerase hC]
    by_cases h1 : r = 1
    · subst r
      rw [show (1 : ℤ) = 1 by norm_num, cpos_one, map_smul, create_ket]
      simp [Wcoord, occ, sign, signExponent, bPrefix, hmem]
    · have h2 : 2 ≤ r := by omega
      have hocc : bSite r ∈ occ B C := (occ_bSite_mem r B C h2).2 hmem
      have hocc' : 2 * (r - 2) ∈ occ B C := by simpa [bSite] using hocc
      rw [cpos_succ r h2, map_smul, annihilate_ket, if_pos hocc']
      simp [Wcoord, occ, sign, signExponent, bPrefix, hmem]
  · by_cases h1 : r = 1
    · subst r
      have hocc : 1 ∉ occ B C := occ_one_mem B C hmem
      rw [show (1 : ℤ) = 1 by norm_num, cpos_one, map_smul, create_ket, if_neg hocc]
      simp [Wcoord, occ, sign, signExponent, bPrefix, hmem]
    · have h2 : 2 ≤ r := by omega
      have hocc' : 2 * (r - 2) ∉ occ B C := by
        intro h
        apply hmem
        exact (occ_bSite_mem r B C h2).1 (by simpa [bSite] using h)
      rw [cpos_succ r h2, map_smul, annihilate_ket, if_neg hocc']
      simp [Wcoord, occ, sign, signExponent, bPrefix, hmem, h1, h2, bSite, hocc']

private theorem cneg_W (r : ℕ) (B C : Finset ℕ)
    (hrpos : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) :
    cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C) := by
  classical
  rw [W_is_Wcoord B C hB hC]
  unfold Wcoord
  by_cases hmem : r ∈ C
  · have hocc : 2 * r + 3 ∈ occ B C := (occ_cSite_mem r B C).2 hmem
    rw [cneg_eq, map_smul, create_ket, if_pos hocc]
    simp [Wcoord, occ, hmem]
  · have hCins : positiveSet (insert r C) := by
      intro t ht
      simp only [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · exact hrpos
      · exact hC t ht
    rw [W_is_Wcoord B (insert r C) hB hCins]
    have hocc' : 2 * r + 3 ∉ occ B C := (occ_cSite_mem r B C).not.mpr hmem
    rw [cneg_eq, map_smul, create_ket, if_neg hocc']
    simp [Wcoord, occ, sign, signExponent, cPrefix, hmem]

private theorem bpos_W (r : ℕ) (B C : Finset ℕ)
    (hrpos : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) :
    b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0 := by
  classical
  rw [W_is_Wcoord B C hB hC]
  unfold Wcoord
  by_cases hmem : r ∈ C
  · have hCerase : positiveSet (C.erase r) := by
      intro t ht
      exact hC t (Finset.mem_of_mem_erase ht)
    rw [W_is_Wcoord B (C.erase r) hB hCerase]
    have hocc : 2 * r + 3 ∈ occ B C := (occ_cSite_mem r B C).2 hmem
    rw [bpos_eq, map_smul, annihilate_ket, if_pos hocc]
    simp [Wcoord, occ, sign, signExponent, cPrefix, hmem]
  · have hocc' : 2 * r + 3 ∉ occ B C := (occ_cSite_mem r B C).not.mpr hmem
    rw [bpos_eq, map_smul, annihilate_ket, if_neg hocc']
    simp [Wcoord, occ, sign, signExponent, cPrefix, hmem]

private theorem native_occupation_projections (r : ℕ) (B C : Finset ℕ)
    (hr : 1 ≤ r) (hB : positiveSet B) (hC : positiveSet C) :
    bneg r (c (r : ℤ) (W B C)) =
      (if r ∈ B then W B C else 0) ∧
    cneg r (b (r : ℤ) (W B C)) =
      (if r ∈ C then W B C else 0) := by
  rw [bneg_W r B C hr hB hC, cpos_W r B C hr hB hC,
    cneg_W r B C hr hB hC, bpos_W r B C hr hB hC]
  by_cases hB : r ∈ B <;> by_cases hC : r ∈ C <;>
    simp [hB, hC, bPrefix, cPrefix, Finset.erase_insert]

private theorem relative_pbw_mode_intertwining :
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C)) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      bneg r (c (r : ℤ) (W B C)) =
      if r ∈ B then W B C else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      cneg r (b (r : ℤ) (W B C)) =
      if r ∈ C then W B C else 0) := by
  exact ⟨bneg_W, cpos_W, cneg_W, bpos_W,
    fun r B C hr hB hC => by
      simpa using (native_occupation_projections r B C hr hB hC).1,
    fun r B C hr hB hC => by
      simpa using (native_occupation_projections r B C hr hB hC).2⟩

private theorem relative_pbw_basis :
    (∀ p : pairCarrier, basisEquiv (Finsupp.single p 1) = Wrel p) ∧
    Function.Bijective basisEquiv := by
  exact ⟨basisEquiv_single, basisEquiv.bijective⟩

theorem relative_pbw_complete :
    (∀ (B C : Finset ℕ), positiveSet B → positiveSet C → W B C = Wcoord B C) ∧
    (∀ p : pairCarrier, basisEquiv (Finsupp.single p 1) = Wrel p) ∧
    Function.Bijective basisEquiv ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C)) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      bneg r (c (r : ℤ) (W B C)) =
      if r ∈ B then W B C else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      cneg r (b (r : ℤ) (W B C)) =
      if r ∈ C then W B C else 0) := by
  rcases relative_pbw_basis with ⟨hunit, hbij⟩
  rcases relative_pbw_mode_intertwining with
    ⟨hbneg, hcpos, hcneg, hbpos, hprojB, hprojC⟩
  exact ⟨W_is_Wcoord, hunit, hbij, hbneg, hcpos, hcneg, hbpos, hprojB, hprojC⟩

end D5.S3.Quantum.Fermionic.BcGhostRelativePBW
