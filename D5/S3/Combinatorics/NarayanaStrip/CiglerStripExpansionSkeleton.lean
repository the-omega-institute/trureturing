/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton
   mirror-E: none(waiver:colored-skeleton-decomposition)
   anchors: []
   utility: none
   digest: Inverse skeleton and colored-gap decomposition of two-colored Motzkin paths. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionSkeleton

open CiglerStripExpansionDefs CiglerStripExpansionPairing

def extractData : List (Bool × Bool) → List Bool × List (List Bool)
  | [] => ([], [[]])
  | (first, second) :: rest =>
    let data := extractData rest
    if first = second then (first :: data.1, [] :: data.2)
    else (data.1, (first :: data.2.headD []) :: data.2.tail)

def insertData : List Bool → List (List Bool) → List (Bool × Bool)
  | skeleton, gap :: gaps =>
    gap.map (fun color => (color, !color)) ++
      match skeleton with
      | [] => []
      | step :: steps => (step, step) :: insertData steps gaps
  | _, [] => []

def gapCharge : Bool → List (List Bool) → ℕ
  | _, [] => 0
  | evenPhase, gap :: gaps =>
    (if evenPhase then 0 else gap.length) + gapCharge (!evenPhase) gaps

theorem skeleton_decomposition :
    ∃ correspondence : List (Bool × Bool) ≃
      {data : List Bool × List (List Bool) // data.2.length = data.1.length + 1},
      (∀ blocks, (correspondence blocks).val = extractData blocks) ∧
      (∀ data, correspondence.symm data = insertData data.val.1 data.val.2) ∧
      (∀ blocks,
        blocks.length = (extractData blocks).1.length +
          (extractData blocks).2.flatten.length) ∧
      (∀ bound blocks, IsMotzkinStrip bound blocks ↔
        IsStripDyck bound (extractData blocks).1) := by
  have extraction_shape (blocks : List (Bool × Bool)) :
      (extractData blocks).2.length = (extractData blocks).1.length + 1 ∧
        insertData (extractData blocks).1 (extractData blocks).2 = blocks ∧
        blocks.length = (extractData blocks).1.length +
          (extractData blocks).2.flatten.length := by
    induction blocks with
    | nil => simp [extractData, insertData]
    | cons block rest induction_hyp =>
      rcases block with ⟨first, second⟩
      have gaps_nonempty : (extractData rest).2 ≠ [] := by
        intro empty
        rw [empty] at induction_hyp
        simp at induction_hyp
      cases data_eq : extractData rest with
      | mk steps gaps =>
        cases gaps with
        | nil => exact False.elim (gaps_nonempty (by simp [data_eq]))
        | cons gap gaps =>
          simp only [data_eq] at induction_hyp
          cases first <;> cases second <;>
            simp [extractData, data_eq, insertData] at induction_hyp ⊢ <;>
            cases steps <;> simp_all [insertData] <;> omega
  have flat_prefix (colors : List Bool) (blocks : List (Bool × Bool)) :
      extractData (colors.map (fun color => (color, !color)) ++ blocks) =
        ((extractData blocks).1,
          (colors ++ (extractData blocks).2.headD []) :: (extractData blocks).2.tail) := by
    have gaps_nonempty : (extractData blocks).2 ≠ [] := by
      intro empty
      have length_eq := (extraction_shape blocks).1
      rw [empty] at length_eq
      simp at length_eq
    induction colors with
    | nil =>
      cases data_eq : extractData blocks with
      | mk skeleton gaps =>
        cases gaps with
        | nil => exact False.elim (gaps_nonempty (by simp [data_eq]))
        | cons gap gaps => simp [data_eq]
    | cons color colors induction_hyp =>
      cases color <;> simp [extractData, induction_hyp]
  have insertion_inverse (skeleton : List Bool) (gaps : List (List Bool))
      (valid : gaps.length = skeleton.length + 1) :
      extractData (insertData skeleton gaps) = (skeleton, gaps) := by
    induction skeleton generalizing gaps with
    | nil =>
      cases gaps with
      | nil => simp at valid
      | cons gap gaps =>
        have empty : gaps = [] := by simpa using valid
        subst gaps
        change extractData (gap.map (fun color => (color, !color)) ++ []) = ([], [gap])
        rw [flat_prefix]
        simp [extractData]
    | cons step steps induction_hyp =>
      cases gaps with
      | nil => simp at valid
      | cons gap gaps =>
        have tail_valid : gaps.length = steps.length + 1 := by simpa using valid
        simp only [insertData, flat_prefix, extractData, if_true]
        rw [induction_hyp gaps tail_valid]
        simp
  have prefix_bounds (bound : ℕ) (height : ℤ) (blocks : List (Bool × Bool)) :
      (∀ index ≤ blocks.length,
        0 ≤ height + coarseHeight blocks index ∧
          height + coarseHeight blocks index ≤ bound) ↔
      (∀ index ≤ (extractData blocks).1.length,
        0 ≤ height + heightAfter (extractData blocks).1 index ∧
          height + heightAfter (extractData blocks).1 index ≤ bound) := by
    induction blocks generalizing height with
    | nil => simp [extractData, heightAfter, coarseHeight]
    | cons block rest induction_hyp =>
      rcases block with ⟨first, second⟩
      have coarse_cons (index : ℕ) :
          coarseHeight ((first, second) :: rest) (index + 1) =
            (if first then (if second then (1 : ℤ) else 0)
              else (if second then 0 else -1)) + coarseHeight rest index := by
        simp [coarseHeight]
      have dyck_cons (step : Bool) (path : List Bool) (index : ℕ) :
          heightAfter (step :: path) (index + 1) =
            (if step then (1 : ℤ) else -1) + heightAfter path index := by
        simp [heightAfter]
      have split_coarse :
          (∀ index ≤ ((first, second) :: rest).length,
            0 ≤ height + coarseHeight ((first, second) :: rest) index ∧
              height + coarseHeight ((first, second) :: rest) index ≤ bound) ↔
          (0 ≤ height ∧ height ≤ bound) ∧
            (∀ index ≤ rest.length,
              0 ≤ (height + (if first then (if second then (1 : ℤ) else 0)
                else (if second then 0 else -1))) + coarseHeight rest index ∧
              (height + (if first then (if second then (1 : ℤ) else 0)
                else (if second then 0 else -1))) + coarseHeight rest index ≤ bound) := by
        constructor
        · intro condition
          constructor
          · simpa [coarseHeight] using condition 0 (by simp)
          · intro index inside
            simpa only [coarse_cons, add_assoc] using condition (index + 1) (by
              simpa using inside)
        · rintro ⟨start, tail_bounds⟩ index inside
          cases index with
          | zero => simpa [coarseHeight] using start
          | succ index =>
            simpa only [coarse_cons, add_assoc] using tail_bounds index (by
              simpa using inside)
      have split_dyck (step : Bool) (path : List Bool) :
          (∀ index ≤ (step :: path).length,
            0 ≤ height + heightAfter (step :: path) index ∧
              height + heightAfter (step :: path) index ≤ bound) ↔
          (0 ≤ height ∧ height ≤ bound) ∧
            (∀ index ≤ path.length,
              0 ≤ (height + (if step then (1 : ℤ) else -1)) + heightAfter path index ∧
                (height + (if step then (1 : ℤ) else -1)) + heightAfter path index ≤
                  bound) := by
        constructor
        · intro condition
          constructor
          · simpa [heightAfter] using condition 0 (by simp)
          · intro index inside
            simpa only [dyck_cons, add_assoc] using condition (index + 1) (by
              simpa using inside)
        · rintro ⟨start, tail_bounds⟩ index inside
          cases index with
          | zero => simpa [heightAfter] using start
          | succ index =>
            simpa only [dyck_cons, add_assoc] using tail_bounds index (by
              simpa using inside)
      rw [split_coarse]
      cases first <;> cases second <;> simp only [extractData, Bool.false_eq_true,
        Bool.true_eq_false, if_false, if_true]
      · rw [split_dyck, induction_hyp]
        simp
      · simp only [add_zero]
        rw [induction_hyp]
        constructor
        · exact fun condition => condition.2
        · intro condition
          exact ⟨by simpa [heightAfter] using condition 0 (by simp), condition⟩
      · simp only [add_zero]
        rw [induction_hyp]
        constructor
        · exact fun condition => condition.2
        · intro condition
          exact ⟨by simpa [heightAfter] using condition 0 (by simp), condition⟩
      · rw [split_dyck, induction_hyp]
        simp
  have endpoint (blocks : List (Bool × Bool)) :
      coarseHeight blocks blocks.length =
        heightAfter (extractData blocks).1 (extractData blocks).1.length := by
    induction blocks with
    | nil => simp [extractData, coarseHeight, heightAfter]
    | cons block rest induction_hyp =>
      rcases block with ⟨first, second⟩
      cases first <;> cases second <;>
        simp [extractData, coarseHeight, heightAfter] at induction_hyp ⊢ <;>
        omega
  let correspondence : List (Bool × Bool) ≃
      {data : List Bool × List (List Bool) // data.2.length = data.1.length + 1} :=
    { toFun := fun blocks => ⟨extractData blocks, (extraction_shape blocks).1⟩
      invFun := fun data => insertData data.val.1 data.val.2
      left_inv := fun blocks => (extraction_shape blocks).2.1
      right_inv := fun data => Subtype.ext (insertion_inverse _ _ data.property) }
  refine ⟨correspondence, fun _ => rfl, fun _ => rfl,
    fun blocks => (extraction_shape blocks).2.2, ?_⟩
  intro bound blocks
  unfold IsMotzkinStrip IsStripDyck
  rw [endpoint]
  have bounds := prefix_bounds bound 0 blocks
  simpa only [zero_add] using and_congr_left (fun _ => bounds)

theorem skeleton_weights (bound : ℕ) (blocks : List (Bool × Bool))
    (valid : IsMotzkinStrip bound blocks) :
    motzkinWeight false 0 blocks =
        Polynomial.X ^ ((extractData blocks).1.count false +
          (extractData blocks).2.flatten.count true) ∧
      motzkinWeight true 0 blocks =
        Polynomial.C ((-1 : ℤ) ^
          ((extractData blocks).1.count false + gapCharge true (extractData blocks).2)) *
          Polynomial.X ^ ((extractData blocks).1.count false +
            (extractData blocks).2.flatten.count true) := by
  have sign_power (height : ℕ) : (-1 : ℤ) ^ height = (-1 : ℤ) ^ (height % 2) := by
    calc
      (-1 : ℤ) ^ height = (-1 : ℤ) ^ (2 * (height / 2) + height % 2) := by
        congr 1
        omega
      _ = (-1 : ℤ) ^ (height % 2) := by simp [pow_add, pow_mul]
  have factorization (height : ℕ) (path : List (Bool × Bool))
      (nonnegative : ∀ index ≤ path.length, 0 ≤ (height : ℤ) + coarseHeight path index) :
      motzkinWeight false height path =
          Polynomial.X ^ ((extractData path).1.count false +
            (extractData path).2.flatten.count true) ∧
        motzkinWeight true height path =
          Polynomial.C ((-1 : ℤ) ^ ((extractData path).1.count false +
            gapCharge (height % 2 == 0) (extractData path).2)) *
            Polynomial.X ^ ((extractData path).1.count false +
              (extractData path).2.flatten.count true) := by
    induction path generalizing height with
    | nil =>
      cases phase : (height % 2 == 0) <;> simp [extractData, motzkinWeight, gapCharge]
    | cons block rest induction_hyp =>
      have gaps_nonempty : (extractData rest).2 ≠ [] := by
        obtain ⟨correspondence, agrees, _⟩ := skeleton_decomposition
        have shape := (correspondence rest).property
        rw [agrees] at shape
        intro empty
        rw [empty] at shape
        simp at shape
      have coarse_cons (index : ℕ) : coarseHeight (block :: rest) (index + 1) =
          (if block.1 then (if block.2 then (1 : ℤ) else 0)
            else (if block.2 then 0 else -1)) + coarseHeight rest index := by
        simp [coarseHeight]
      have rest_nonnegative : ∀ index ≤ rest.length,
          0 ≤ (height : ℤ) +
            (if block.1 then (if block.2 then (1 : ℤ) else 0)
              else (if block.2 then 0 else -1)) + coarseHeight rest index := by
        intro index inside
        have lower := nonnegative (index + 1) (by simpa using inside)
        rw [coarse_cons] at lower
        simpa only [add_assoc] using lower
      cases data_eq : extractData rest with
      | mk skeleton gaps =>
        cases gaps with
        | nil => exact False.elim (gaps_nonempty (by simp [data_eq]))
        | cons gap gaps =>
          rcases block with ⟨first, second⟩
          cases first <;> cases second
          · have height_positive : 1 ≤ height := by
              have lower := nonnegative 1 (by simp)
              simp [coarseHeight] at lower
              omega
            have lower : ∀ index ≤ rest.length,
                0 ≤ ((height - 1 : ℕ) : ℤ) + coarseHeight rest index := by
              intro index inside
              have lower := rest_nonnegative index inside
              simp only [Bool.false_eq_true, if_false] at lower
              omega
            have recurse := induction_hyp (height - 1) lower
            simp only [data_eq] at recurse
            have opposite : ((height - 1) % 2 == 0) = !(height % 2 == 0) := by
              rcases Nat.mod_two_eq_zero_or_one height with parity | parity
              · have before : (height - 1) % 2 = 1 := by omega
                simp [before, parity]
              · have before : (height - 1) % 2 = 0 := by omega
                simp [before, parity]
            rw [opposite] at recurse
            cases phase : (height % 2 == 0) <;>
              simp [motzkinWeight, extractData, data_eq, gapCharge, phase, recurse.1,
                recurse.2, pow_add, mul_comm, mul_left_comm, mul_assoc]
          · have lower : ∀ index ≤ rest.length,
                0 ≤ (height : ℤ) + coarseHeight rest index := by
              simpa using rest_nonnegative
            have recurse := induction_hyp height lower
            simp only [data_eq] at recurse
            simp only [motzkinWeight]
            rw [sign_power height]
            rcases Nat.mod_two_eq_zero_or_one height with parity | parity <;>
              simp [extractData, data_eq, gapCharge, parity, recurse.1,
                recurse.2, pow_add, mul_comm, mul_left_comm, mul_assoc]
          · have lower : ∀ index ≤ rest.length,
                0 ≤ (height : ℤ) + coarseHeight rest index := by
              simpa using rest_nonnegative
            have recurse := induction_hyp height lower
            simp only [data_eq] at recurse
            simp only [motzkinWeight]
            rw [sign_power height]
            rcases Nat.mod_two_eq_zero_or_one height with parity | parity <;>
              simp [extractData, data_eq, gapCharge, parity, recurse.1,
                recurse.2, pow_add, mul_comm, mul_left_comm, mul_assoc]
          · have lower : ∀ index ≤ rest.length,
                0 ≤ ((height + 1 : ℕ) : ℤ) + coarseHeight rest index := by
              simpa [add_assoc] using rest_nonnegative
            have recurse := induction_hyp (height + 1) lower
            simp only [data_eq] at recurse
            have opposite : ((height + 1) % 2 == 0) = !(height % 2 == 0) := by
              rcases Nat.mod_two_eq_zero_or_one height with parity | parity
              · have after : (height + 1) % 2 = 1 := by omega
                simp [after, parity]
              · have after : (height + 1) % 2 = 0 := by omega
                simp [after, parity]
            rw [opposite] at recurse
            cases phase : (height % 2 == 0) <;>
              simp [motzkinWeight, extractData, data_eq, gapCharge, phase, recurse.1, recurse.2]
  simpa using factorization 0 blocks (by
    intro index inside
    simpa using (valid.1 index inside).1)

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionSkeleton
