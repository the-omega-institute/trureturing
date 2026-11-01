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

@[simp] theorem down_eq : down = ket {1} := ghost_vacuum.2.2.1

def relative : Submodule ℂ Fock := LinearMap.ker (b 0)

def gword : List (Module.End ℂ Fock) → Module.End ℂ Fock
  | [] => 1
  | a :: w => a * gword w

def bneg (r : ℕ) : Module.End ℂ Fock := b (-(r : ℤ))

def cneg (r : ℕ) : Module.End ℂ Fock := c (-(r : ℤ))

@[simp] theorem bneg_one : bneg 1 = annihilate 1 := by
  simp [bneg, b]

theorem bneg_succ (r : ℕ) (hr : 2 ≤ r) :
    bneg r = create (2 * (r - 2)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
  simp [bneg, b]

@[simp] theorem cneg_eq (r : ℕ) : cneg r = create (2 * r + 3) := by
  simp [cneg, c]

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

theorem gword_append (xs ys : List (Module.End ℂ Fock)) :
    gword (xs ++ ys) = gword xs * gword ys := by
  induction xs with
  | nil => simp [gword]
  | cons x xs ih => simp [gword, ih, mul_assoc]

theorem W_eq_bword_cword (B C : Finset ℕ) :
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
      have htail := cword_sorted xs hsort.pairwise hnodup.tail
      have hxnot : x ∉ xs := (List.nodup_cons.mp hnodup).1
      rw [gword, List.map_cons, htail, cneg_eq, create_ket]
      have hx : 2 * x + 3 ∉ cOcc xs := by
        intro hx
        simp only [cOcc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hx
        rcases hx with hx | ⟨y, hy, he⟩
        · omega
        · have hxy : x < y := hsort.head y hy
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
            · have hxy : x < y := hsort.head y hy
              exact False.elim (by omega)
          · intro hj
            subst j
            constructor
            · exact Or.inl rfl
            · omega
        rw [heq]
        simp
      rw [show phase (2 * x + 3) (cOcc xs) = (-1 : ℂ) by
        simp [phase, hcount]]
      have hset : insert (2 * x + 3) (cOcc xs) = cOcc (x :: xs) := by
        simp [cOcc, hxnot]
      rw [hset, smul_smul, pow_succ]
      ring

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
      simp [Finset.product_insert, hr]

private theorem bword_sorted : ∀ (xs : List ℕ) (C : Finset ℕ),
    xs.Pairwise (· < ·) → xs.Nodup → (∀ r ∈ xs, 2 ≤ r) →
    gword (xs.map bneg) (ket (cOcc (asc C))) =
      (-1 : ℂ) ^ (xs.toFinset.sum (fun r => bStepExponent r C)) •
        ket (bOcc C xs)
  | [], C, _, _, _ => by simp [gword, bOcc]
  | x :: xs, C, hsort, hnodup, htwo => by
      have htail := bword_sorted xs C hsort.pairwise hnodup.tail
        (fun r hr => htwo r (by simp [hr]))
      have hxnot : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hx2 : 2 ≤ x := htwo x (by simp)
      rw [gword, List.map_cons, htail, bneg_succ x hx2, create_ket]
      have heven : bSite x ∉ bOcc C xs := by
        intro hx
        simp only [bOcc, Finset.mem_union, Finset.mem_image] at hx
        rcases hx with hx | ⟨y, hy, he⟩
        · simp only [cOcc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hx
          rcases hx with hx | ⟨s, hs, hse⟩
          · simp [bSite] at hx
          · simp [bSite] at hse
        · have hxy : x < y := hsort.head y hy
          simp [bSite] at he
          omega
      rw [if_neg heven]
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
                · simp [hx3]
                · simp [hx3] at hlt
              · by_cases hs4 : s + 4 ≤ x
                · simp [hs4]
                · simp [hs4] at hlt
            · have hxy : x < y := hsort.head y hy
              simp [bSite] at hlt
              omega
          · intro hj
            rcases hj with hj | ⟨s, hs, rfl⟩
            · have hx3 : 3 ≤ x := by simpa using hj
              constructor
              · exact Or.inl (Or.inl rfl)
              · omega
            · have hs4 : s + 4 ≤ x := by simpa using hs
              constructor
              · exact Or.inl (Or.inr ⟨s, (Finset.mem_filter.mp hs).1, rfl⟩)
              · omega
        rw [heq]
        simp [Finset.card_union_of_disjoint]
      rw [show phase (bSite x) (bOcc C xs) = (-1 : ℂ) ^ bStepExponent x C by
        simp [phase, hcount]]
      have hset : insert (bSite x) (bOcc C xs) = bOcc C (x :: xs) := by
        simp [bOcc, bSite, hxnot]
      rw [hset, smul_smul, ← pow_add]
      congr 1
      simp [bStepExponent, Finset.sum_insert hxnot]

private theorem bword_asc (B C : Finset ℕ) (hB : 1 ∉ B) :
    gword ((asc B).map bneg) (ket (cOcc (asc C))) =
      (-1 : ℂ) ^ ((B.filter (fun r => 3 ≤ r)).card +
        ((B.product C).filter (fun p => p.2 + 4 ≤ p.1)).card) •
        ket (cOcc (asc C) ∪ (B.image bSite)) := by
  have htwo : ∀ r ∈ asc B, 2 ≤ r := by
    intro r hr
    have hrB : r ∈ B := by simpa [asc] using hr
    have hrne : r ≠ 1 := by intro h; subst r; exact hB hrB
    omega
  rw [bword_sorted (asc B) C (asc_sorted B) (asc_nodup B) htwo]
  congr 1
  · have hsort : (asc B).toFinset = B := by
      exact Finset.sort_toFinset _ _
    rw [hsort]
    simp only [bStepExponent, Finset.sum_add_distrib]
    rw [sum_ge_three, sum_crossing]
  · simp [bOcc, asc]

private theorem asc_insert_one (B : Finset ℕ) (hB : 1 ∉ B) :
    asc (insert 1 B) = 1 :: asc B := by
  unfold asc
  apply Finset.sort_insert
  · intro r hr
    omega
  · exact hB

private theorem bword_erase_one (B C : Finset ℕ) (hB : 1 ∈ B) :
    gword ((asc (B.erase 1)).map bneg) (ket (cOcc (asc C))) =
      (-1 : ℂ) ^ ((B.filter (fun r => 3 ≤ r)).card +
        ((B.product C).filter (fun p => p.2 + 4 ≤ p.1)).card) •
        ket (cOcc (asc C) ∪ ((B.erase 1).image bSite)) := by
  apply bword_asc (B.erase 1) C
  exact Finset.notMem_erase 1 B

private theorem W_is_Wcoord (B C : Finset ℕ) : W B C = Wcoord B C := by
  classical
  rw [W_eq_bword_cword, cword_asc]
  by_cases hB : 1 ∈ B
  · rw [show B = insert 1 (B.erase 1) by exact (Finset.insert_erase hB).symm,
      asc_insert_one (B.erase 1) (Finset.notMem_erase 1 B)]
    rw [gword, bneg_one, map_smul, annihilate_ket]
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
          · simp only [h2, Finset.mem_singleton] at hj
            subst j
            constructor
            · exact ⟨Or.inr ⟨2, Finset.mem_erase.mpr ⟨by omega, h2⟩, by simp [bSite]⟩⟩
            · omega
          · simp [h2] at hj
      simp [phase, lowerCount, hfilter]
    rw [hphase, smul_smul]
    have hset : (cOcc (asc C) ∪ (B.erase 1).image bSite).erase 1 = occ B C := by
      ext j
      simp only [occ, cOcc, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨hne, hj | ⟨r, hr, rfl⟩⟩
        · rcases hj with hj | ⟨s, hs, rfl⟩
          · omega
          · exact Or.inr (Or.inr ⟨s, by simpa [asc] using hs, rfl⟩)
        · right
          left
          refine ⟨r, ?_, rfl⟩
          exact ⟨by omega, hr⟩
      · intro hj
        rcases hj with hj | ⟨r, hr, rfl⟩
        · simp at hj
        · rcases hj with hr2 | ⟨s, hs, rfl⟩
          · exact ⟨by omega, Or.inr ⟨r, Finset.mem_erase.mpr ⟨by omega, hr⟩, by simp [bSite]⟩⟩
          · exact ⟨by omega, Or.inl (Or.inr ⟨s, by simpa [asc] using hs, rfl⟩)⟩
    rw [hset]
    unfold Wcoord sign signExponent
    simp [hB]
  · have hErase : B.erase 1 = B := Finset.erase_eq_of_not_mem hB
    rw [hErase]
    unfold Wcoord sign signExponent occ bOcc
    simp [hB, cOcc, asc]

def invB (S : Finset ℕ) : Finset ℕ :=
  (if 1 ∉ S then {1} else ∅) ∪
    (S.filter (fun j => j % 2 = 0)).image (fun j => j / 2 + 2)

def invC (S : Finset ℕ) : Finset ℕ :=
  (S.filter (fun j => j % 2 = 1 ∧ 5 ≤ j)).image (fun j => j / 2 - 1)

def pairCarrier := {p : Finset ℕ × Finset ℕ // 3 ∉ occ p.1 p.2}

def pairToOcc (p : pairCarrier) : Finset ℕ := occ p.1 p.2

def occupationCarrier := {S : Finset ℕ // 3 ∉ S}

def pairToOccupation (p : pairCarrier) : occupationCarrier := ⟨pairToOcc p, p.2⟩

def occToPair (S : Finset ℕ) : pairCarrier :=
  ⟨(invB S, invC S), by simp [occ, invB, invC]
    <;> aesop⟩

theorem invB_occ (B C : Finset ℕ) (h3 : 3 ∉ occ B C) : invB (occ B C) = B := by
  ext r
  simp [invB, occ]
  omega

theorem invC_occ (B C : Finset ℕ) (h3 : 3 ∉ occ B C) : invC (occ B C) = C := by
  ext s
  simp [invC, occ]
  omega

theorem occ_inv (S : Finset ℕ) (h3 : 3 ∉ S) : occ (invB S) (invC S) = S := by
  ext j
  simp [occ, invB, invC]
  omega

def pairOccupationEquiv : pairCarrier ≃ occupationCarrier where
  toFun := pairToOccupation
  invFun := fun S => occToPair S.1
  left_inv := by
    intro p
    apply Subtype.ext
    simp only [occToPair, pairToOccupation, Subtype.mk.injEq]
    rw [invB_occ, invC_occ]
    exact Subtype.prop p
  right_inv := by
    intro S
    apply Subtype.ext
    exact occ_inv S.1 S.2

private theorem W_mem_relative (B C : Finset ℕ) : W B C ∈ relative := by
  rw [W_is_Wcoord, down_eq]
  simp [relative, occ, Wcoord, b, c, sign]

def Wrel (p : pairCarrier) : relative := ⟨W p.1 p.2, W_mem_relative p.1 p.2⟩

theorem relative_coeff_three (v : relative) {S : Finset ℕ} (hS : 3 ∈ S) :
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

def allowed : Set (Finset ℕ) := {S | 3 ∉ S}

def supportedAllowed : Submodule ℂ Fock := Finsupp.supported ℂ ℂ allowed

private theorem no_three_annihilate (v : Fock)
    (h : ∀ S ∈ v.support, 3 ∉ S) : annihilate 3 v = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single S a =>
      by_cases hS : 3 ∈ S
      · exact False.elim (h S (by simp [hS]) hS)
      · simp [map_smul, annihilate_ket, hS]

theorem relative_eq_supportedAllowed : relative = supportedAllowed := by
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
    (sign p.1 p.2 • Finsupp.single p 1))

private theorem signMap_involution : signMap.comp signMap = LinearMap.id := by
  apply LinearMap.ext
  intro v
  induction v using Finsupp.induction_linear with
  | zero => simp [signMap]
  | add f g hf hg => simp [map_add, hf, hg]
  | single p a =>
      simp [signMap, sign, ← pow_add]

def signEquiv : (pairCarrier →₀ ℂ) ≃ₗ[ℂ] (pairCarrier →₀ ℂ) :=
  LinearEquiv.ofBijective signMap ⟨
    (fun x y h => by
      have := congrArg signMap h
      simpa [signMap_involution] using this),
    (fun y => ⟨signMap y, by simpa [signMap_involution]⟩)⟩

def basisEquiv : (pairCarrier →₀ ℂ) ≃ₗ[ℂ] relative :=
  signEquiv ≪≫ₗ Finsupp.mapDomain.linearEquiv ℂ ℂ pairOccupationEquiv ≪≫ₗ ketEquiv

private theorem basisEquiv_single (p : pairCarrier) :
    basisEquiv (Finsupp.single p 1) = Wrel p := by
  apply Subtype.ext
  rw [basisEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  simp [signEquiv, signMap, ketEquiv, Wrel, W_is_Wcoord]

private theorem pairToOcc_injective : Function.Injective pairToOcc := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · rw [← invB_occ p.1.1 p.1.2 p.2, ← invB_occ q.1.1 q.1.2 q.2, h]
  · rw [← invC_occ p.1.1 p.1.2 p.2, ← invC_occ q.1.1 q.1.2 q.2, h]


def bPrefix (r : ℕ) (B : Finset ℕ) : ℕ := (B.filter (fun t => t < r)).card

def cPrefix (r : ℕ) (C : Finset ℕ) : ℕ := (C.filter (fun t => t < r)).card

private theorem bneg_W (r : ℕ) (B C : Finset ℕ) :
    bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C := by
  classical
  rw [W_is_Wcoord]
  by_cases hr : r ∈ B
  · simp [Wcoord, bneg, b, occ, hr]
  · by_cases h1 : r = 1
    · subst r
      simp [Wcoord, bneg, b, occ, sign, signExponent, bPrefix, hr]
    · have h2 : 2 ≤ r := by omega
      simp [Wcoord, bneg, b, occ, sign, signExponent, bPrefix, hr, h1, h2,
        bSite]

private theorem cpos_W (r : ℕ) (B C : Finset ℕ) :
    c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0 := by
  classical
  rw [W_is_Wcoord]
  by_cases hr : r ∈ B
  · simp [Wcoord, c, occ, sign, signExponent, bPrefix, hr]
  · by_cases h1 : r = 1
    · subst r
      simp [Wcoord, c, occ, sign, signExponent, bPrefix, hr]
    · have h2 : 2 ≤ r := by omega
      simp [Wcoord, c, occ, sign, signExponent, bPrefix, hr, h1, h2,
        bSite]

private theorem cneg_W (r : ℕ) (B C : Finset ℕ) :
    cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C) := by
  classical
  rw [W_is_Wcoord]
  by_cases hr : r ∈ C
  · simp [Wcoord, cneg, c, occ, hr]
  · simp [Wcoord, cneg, c, occ, sign, signExponent, cPrefix, hr]

private theorem bpos_W (r : ℕ) (B C : Finset ℕ) :
    b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0 := by
  classical
  rw [W_is_Wcoord]
  by_cases hr : r ∈ C
  · simp [Wcoord, b, occ, sign, signExponent, cPrefix, hr]
  · simp [Wcoord, b, occ, sign, signExponent, cPrefix, hr]

private theorem bneg_cpos_intertwining (r : ℕ) :
    ∀ B C, bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C :=
  bneg_W r

private theorem native_occupation_projections (r : ℕ) (B C : Finset ℕ) :
    bneg r (c (r : ℤ) (W B C)) =
      (if r ∈ B then W B C else 0) ∧
    cneg r (b (r : ℤ) (W B C)) =
      (if r ∈ C then W B C else 0) := by
  rw [bneg_W, cpos_W, cneg_W, bpos_W]
  by_cases hB : r ∈ B <;> by_cases hC : r ∈ C <;>
    simp [hB, hC, bPrefix, cPrefix, Finset.erase_insert]

private theorem positive_modes_kill_down :
    (∀ r : ℕ, b (r : ℤ) down = 0) ∧
    (∀ r : ℤ, 2 ≤ r → c r down = 0) := by
  rw [down_eq]
  constructor
  · intro r
    have h : ¬(r : ℤ) ≤ -2 := by omega
    simp [b, h, annihilate_ket]
  · intro r hr
    have h : ¬r ≤ 1 := by omega
    simp [c, h, annihilate_ket]

private theorem relative_pbw_mode_intertwining :
    (∀ r B C, bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C) ∧
    (∀ r B C, c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0) ∧
    (∀ r B C, cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C)) ∧
    (∀ r B C, b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0) ∧
    (∀ r B C, bneg r (c (r : ℤ) (W B C)) =
      if r ∈ B then W B C else 0) ∧
    (∀ r B C, cneg r (b (r : ℤ) (W B C)) =
      if r ∈ C then W B C else 0) := by
  exact ⟨bneg_W, cpos_W, cneg_W, bpos_W,
    fun r B C => by
      simpa using (native_occupation_projections r B C).1,
    fun r B C => by
      simpa using (native_occupation_projections r B C).2⟩

private theorem relative_pbw_basis :
    (∀ p : pairCarrier, basisEquiv (Finsupp.single p 1) = Wrel p) ∧
    Function.Bijective basisEquiv := by
  exact ⟨basisEquiv_single, basisEquiv.bijective⟩

theorem relative_pbw_complete :
    (∀ B C : Finset ℕ, W B C = Wcoord B C) ∧
    (∀ p : pairCarrier, basisEquiv (Finsupp.single p 1) = Wrel p) ∧
    Function.Bijective basisEquiv ∧
    (∀ r B C, bneg r (W B C) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C) ∧
    (∀ r B C, c (r : ℤ) (W B C) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0) ∧
    (∀ r B C, cneg r (W B C) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C)) ∧
    (∀ r B C, b (r : ℤ) (W B C) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0) ∧
    (∀ r B C, bneg r (c (r : ℤ) (W B C)) =
      if r ∈ B then W B C else 0) ∧
    (∀ r B C, cneg r (b (r : ℤ) (W B C)) =
      if r ∈ C then W B C else 0) := by
  rcases relative_pbw_basis with ⟨hunit, hbij⟩
  rcases relative_pbw_mode_intertwining with
    ⟨hbneg, hcpos, hcneg, hbpos, hprojB, hprojC⟩
  exact ⟨W_is_Wcoord, hunit, hbij, hbneg, hcpos, hcneg, hbpos, hprojB, hprojC⟩

private example : W ∅ ∅ = ket {1} := by
  rw [W_is_Wcoord]
  simp [Wcoord, sign, occ]

private example : W {1} {2} = -ket {7} := by
  rw [W_is_Wcoord]
  norm_num [Wcoord, sign, signExponent, occ]

private example : W {1, 2} ∅ = -ket ∅ := by
  rw [W_is_Wcoord]
  norm_num [Wcoord, sign, signExponent, occ]

private example : W {5} {1} = -ket {1, 5, 6} := by
  rw [W_is_Wcoord]
  norm_num [Wcoord, sign, signExponent, occ]

end D5.S3.Quantum.Fermionic.BcGhostRelativePBW
