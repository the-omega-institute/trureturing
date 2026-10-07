/- GID: D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual tree images realize every finite hereditary information-leaf pattern. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import Mathlib.Data.Finset.Max
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.UpperLower.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.FiniteHereditaryPatternRealization

open GenealogicalFiberTransport (Source substitution composition)
open ActualImageAddressCertificate (ActualImage)
open ActualTreeReadoutAcquisition (Address Reply readout leaves)
open ActualImageSevenLeafSeparation (leafAddresses leafLabel)
open scoped BigOperators

/-- The three blocks in a column. -/
inductive Block | a | u | v

/-- Literal complete preimages of the three blocks. -/
def preimage : Block → Source
  | .a => .of true
  | .u => .mul (.mul (.of true) (.of true)) (.of false)
  | .v => .mul (.mul (.of true) (.of false)) (.of true)

local notation "block" => (fun b : Block => ActualImageSevenLeafSeparation.thirdImage (preimage b))

/-- Information leaves are shared leaves bearing both labels among the indices. -/
def Delta {ι : Type*} (P : ι → Source) (S : Finset ι) : Set Address :=
  {w | (∀ i ∈ S, readout w (P i) = .alpha ∨ readout w (P i) = .beta) ∧
    (∃ i ∈ S, readout w (P i) = .alpha) ∧ ∃ i ∈ S, readout w (P i) = .beta}

/-- Residual information leaves shared by U and V. -/
def D : Set Address := Delta (fun b : Bool => if b then block .u else block .v) Finset.univ

/-- A column contributes precisely when it contains U and V and contains no A. -/
def Mixed {ι : Type*} (X : ι → Block) (S : Finset ι) : Prop :=
  (∀ i ∈ S, X i ≠ .a) ∧ (∃ i ∈ S, X i = .u) ∧ ∃ i ∈ S, X i = .v

/-- Right-comb context with n+1 holes and no literal leaves. -/
def B_T : (n : ℕ) → (Fin (n + 1) → Source) → Source
  | 0, X => X 0
  | n + 1, X => .mul (X 0) (B_T n (fun j => X j.succ))

/-- Root-first hole addresses in the right-comb context. -/
def hole : (n : ℕ) → Fin (n + 1) → Address
  | 0, _ => []
  | n + 1, j => Fin.cases [false] (fun k => true :: hole n k) j

/-- None denotes an internal context node; some records the unique hole and suffix. -/
def locate : (n : ℕ) → Address → Option (Fin (n + 1) × Address)
  | 0, w => some (0, w)
  | n + 1, [] => none
  | n + 1, false :: v => some (0, v)
  | n + 1, true :: v => (locate n v).map (fun p => (p.1.succ, p.2))

/-- The complete set of inclusion-maximal faces. -/
noncomputable def maximalFaces {m : ℕ} (K : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  by classical exact K.filter (fun F => ∀ G ∈ K, F ⊆ G → G = F)

/-- Original columns (F,k), with F maximal and k in F. -/
abbrev FaceColumn {m : ℕ} (K : Finset (Finset (Fin m))) :=
  {p : Finset (Fin m) × Fin m // p.1 ∈ maximalFaces K ∧ p.2 ∈ p.1}

/-- Each maximal face supplies one V entry and U entries at its other indices. -/
def faceEntry {m : ℕ} {K : Finset (Finset (Fin m))} (i : Fin m) (c : FaceColumn K) : Block :=
  if i = c.val.2 then .v else if i ∈ c.val.1 then .u else .a

/-- Number of non-A original entries in a row. -/
noncomputable def rowCount {m : ℕ} (K : Finset (Finset (Fin m))) (i : Fin m) : ℕ :=
  by
    classical
    letI := Fintype.ofFinite (FaceColumn K)
    exact (Finset.univ.filter (fun c : FaceColumn K => i ∈ c.val.1)).card

/-- Maximum original non-A row count. -/
noncomputable def M {m : ℕ} (K : Finset (Finset (Fin m))) : ℕ :=
  Finset.univ.sup (rowCount K)

/-- Private-row padding columns, one for each missing non-A entry. -/
abbrev PaddingColumn {m : ℕ} (K : Finset (Finset (Fin m))) :=
  Σ i : Fin m, Fin (M K - rowCount K i)

/-- Original and padding columns together, before choosing their order. -/
abbrev Column {m : ℕ} (K : Finset (Finset (Fin m))) := FaceColumn K ⊕ PaddingColumn K

/-- Padding puts U in its owner's row and A in every other row. -/
def entry {m : ℕ} {K : Finset (Finset (Fin m))} (i : Fin m) : Column K → Block
  | .inl c => faceEntry i c
  | .inr c => if i = c.1 then .u else .a


/-- Composition of the complete right-comb hole table. -/
theorem composition_comb (n : ℕ) (X : Fin (n + 1) → Source) :
    composition (B_T n X) = ∑ j, composition (X j) := by
  induction n with
  | zero => simp [B_T]
  | succ n hn =>
    rw [B_T, composition, hn]
    exact (Fin.sum_univ_succ (fun j : Fin (n + 2) => composition (X j))).symm

set_option maxHeartbeats 2000000 in -- Full address decomposition and finite face-table construction.
/-- Right-comb block reports and the equal-composition actual realization of every
finite hereditary family containing the singleton faces. -/
theorem result :
    (∀ n : ℕ, ∀ X : Fin (n + 1) → Source, ∀ w : Address,
      readout w (B_T n X) = match locate n w with
        | none => .branch
        | some p => readout p.2 (X p.1)) ∧
    (∀ n : ℕ, ∀ w : Address, locate n w = none ↔
      ∃ j : Fin (n + 1), ∃ r : Address, r ≠ [] ∧ hole n j = w ++ r) ∧
    (∀ m n : ℕ, ∀ X : Fin m → Fin (n + 1) → Block, ∀ S : Finset (Fin m), ∀ w : Address,
      w ∈ Delta (fun i => B_T n (fun j => block (X i j))) S ↔
        ∃ j v, w = hole n j ++ v ∧ Mixed (fun i => X i j) S ∧ v ∈ D) ∧
    (∀ n : ℕ, ∀ j k : Fin (n + 1), ∀ v u : Address,
      hole n j ++ v = hole n k ++ u → j = k ∧ v = u) ∧
    (∀ m : ℕ, 2 ≤ m → ∀ K : Finset (Finset (Fin m)), IsLowerSet (K : Set (Finset (Fin m))) →
      (∀ i : Fin m, {i} ∈ K) →
        let T := Nat.card (Column K)
        let N := M K
        1 ≤ T ∧ ∀ e : Fin (T - 1 + 1) ≃ Column K,
        let Q : Fin m → Source := fun i => B_T (T - 1) (fun j => preimage (entry i (e j)))
        let P : Fin m → Source := fun i => B_T (T - 1) (fun j => block (entry i (e j)))
        Function.Injective Q ∧ Function.Injective P ∧
        (∀ i, substitution^[3] (Q i) = P i ∧ P i ∈ ActualImage 3 ∧
          composition (Q i) = (T + N, N) ∧
          composition (P i) = (T + 3 * N, 2 * T + 5 * N) ∧
          (composition (P i)).1 + (composition (P i)).2 = 3 * T + 8 * N) ∧
        (∀ i R, substitution^[3] R = P i ↔ R = Q i) ∧
        (∀ S : Finset (Fin m), 2 ≤ S.card → ((Delta P S).Nonempty ↔ S ∈ K))) := by
  classical
  have maximal_contains {m : ℕ} (K : Finset (Finset (Fin m))) (S : Finset (Fin m)) (hS : S ∈ K) :
      ∃ F ∈ maximalFaces K, S ⊆ F := by
    obtain ⟨F, hSF, hF⟩ := K.exists_le_maximal hS
    exact ⟨F, Finset.mem_filter.mpr ⟨hF.1,
      fun G hG hFG => Finset.Subset.antisymm (hF.2 hG hFG) hFG⟩, hSF⟩
  have face_non_a {m : ℕ} {K : Finset (Finset (Fin m))} (i : Fin m) (c : FaceColumn K) :
      faceEntry i c ≠ .a ↔ i ∈ c.val.1 := by
    by_cases hi : i = c.val.2
    · subst i
      simp [faceEntry, c.property.2]
    · simp [faceEntry, hi]

  have address_facts :
      (∀ n : ℕ, ∀ X : Fin (n + 1) → Source, ∀ w : Address,
        readout w (B_T n X) = match locate n w with
          | none => .branch
          | some p => readout p.2 (X p.1)) ∧
      (∀ n : ℕ, ∀ j : Fin (n + 1), ∀ v : Address,
        locate n (hole n j ++ v) = some (j, v)) ∧
      (∀ n : ℕ, ∀ w : Address, ∀ j : Fin (n + 1), ∀ v : Address,
        locate n w = some (j, v) ↔ w = hole n j ++ v) := by
    classical
    have read (n : ℕ) (X : Fin (n + 1) → Source) (w : Address) :
        readout w (B_T n X) = match locate n w with
          | none => .branch
          | some p => readout p.2 (X p.1) := by
      induction n generalizing w with
      | zero => rfl
      | succ n hn =>
        cases w with
        | nil => rfl
        | cons b w =>
          cases b with
          | false => rfl
          | true =>
            have h := hn (fun j => X j.succ) w
            cases hl : locate n w <;> simpa [B_T, locate, readout, hl] using h
    have hole_locate (n : ℕ) (j : Fin (n + 1)) (v : Address) :
        locate n (hole n j ++ v) = some (j, v) := by
      induction n with
      | zero => have hj : j = 0 := Fin.eq_zero j; subst j; rfl
      | succ n hn =>
        refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · simpa [hole, locate] using congrArg
            (fun p : Option (Fin (n + 1) × Address) => p.map (fun q => (q.1.succ, q.2)))
            (hn k)
    have locate_eq (n : ℕ) (w : Address) (j : Fin (n + 1)) (v : Address) :
        locate n w = some (j, v) ↔ w = hole n j ++ v := by
      induction n generalizing w with
      | zero =>
        have hj : j = 0 := Fin.eq_zero j
        subst j
        simp [locate, hole]
      | succ n hn =>
        refine Fin.cases ?_ (fun k => ?_) j
        · cases w with
          | nil => simp [locate, hole]
          | cons b w =>
            cases b with
            | false => simp [locate, hole]
            | true =>
              cases hl : locate n w <;> simp [locate, hole, hl, Fin.succ_ne_zero]
        · cases w with
          | nil => simp [locate, hole]
          | cons b w =>
            cases b with
            | false =>
              have hne : (0 : Fin (n + 2)) ≠ k.succ := Ne.symm (Fin.succ_ne_zero k)
              simp [locate, hole, hne]
            | true =>
              cases hl : locate n w with
              | none => simp [locate, hole, hl, ← hn w k]
              | some p =>
                rcases p with ⟨a, u⟩
                simpa [locate, hole, hl, ← hn w k] using
                  (show (a = k ∧ u = v) ↔ (a = k ∧ u = v) from Iff.rfl)
    exact ⟨read, hole_locate, locate_eq⟩

  have face_facts (m : ℕ) (hm : 2 ≤ m) (K : Finset (Finset (Fin m)))
      (hK : IsLowerSet (K : Set (Finset (Fin m)))) (hsingle : ∀ i : Fin m, {i} ∈ K) :
      ∀ S : Finset (Fin m), 2 ≤ S.card →
        ((∃ c : Column K, Mixed (fun i => entry i c) S) ↔ S ∈ K) := by
    classical
    intro S hcard
    constructor
    · rintro ⟨c, hc⟩
      cases c with
      | inl c =>
        apply hK _ (Finset.mem_filter.mp c.property.1).1
        intro i hi
        exact (face_non_a i c).mp (hc.1 i hi)
      | inr c =>
        obtain ⟨i, hi, hv⟩ := hc.2.2
        change (if i = c.1 then Block.u else Block.a) = .v at hv
        split_ifs at hv <;> cases hv
    · intro hS
      obtain ⟨F, hF, hSF⟩ := maximal_contains K S hS
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      obtain ⟨j, hj, hjk⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) k
      let c : FaceColumn K := ⟨(F, k), hF, hSF hk⟩
      refine ⟨.inl c, ?_, ⟨j, hj, ?_⟩, ⟨k, hk, ?_⟩⟩
      · intro i hi
        exact (face_non_a i c).mpr (hSF hi)
      · simp [entry, faceEntry, c, hjk, hSF hj]
      · simp [entry, faceEntry, c]

  have block_facts :
      [false, true, false, true] ∈ D ∧
      (∀ {ι : Type} (X : ι → Block) (S : Finset ι) (w : Address),
        w ∈ Delta (fun i => block (X i)) S ↔ Mixed X S ∧ w ∈ D) := by
    classical
    have a_leaf (w : Address) :
        (readout w (block .a) = .alpha ∨ readout w (block .a) = .beta) ↔
        w = [false, false] ∨ w = [false, true] ∨ w = [true] := by
      have semantics := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (block .a)).2 w
      have labelled : (∃ b, leafLabel (block .a) w = some b) ↔
          readout w (block .a) = .alpha ∨ readout w (block .a) = .beta := by
        cases hr : readout w (block .a) <;> simp [leafLabel, hr]
      rw [← labelled, ← semantics]
      simp [leafAddresses, leaves, ActualImageSevenLeafSeparation.thirdImage, preimage,
        Function.iterate_succ_apply', substitution]
    have incompatible (b : Block) (hb : b ≠ .a) (w : Address)
        (ha : readout w (block .a) = .alpha ∨ readout w (block .a) = .beta) :
        ¬ (readout w (block b) = .alpha ∨ readout w (block b) = .beta) := by
      rcases (a_leaf w).mp ha with rfl | rfl | rfl <;>
        cases b <;> simp_all [ActualImageSevenLeafSeparation.thirdImage, preimage, readout,
          Function.iterate_succ_apply', substitution]
    have D_spec (w : Address) : w ∈ D ↔
        (readout w (block .u) = .alpha ∧ readout w (block .v) = .beta) ∨
        (readout w (block .u) = .beta ∧ readout w (block .v) = .alpha) := by
      simp only [D, Delta, Set.mem_setOf_eq, Finset.mem_univ, forall_true_left,
        Bool.forall_bool, Bool.exists_bool, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨⟨hv, hu⟩, ha, hb⟩
        rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp_all
      · rintro (⟨hu, hv⟩ | ⟨hu, hv⟩) <;> simp_all
    refine ⟨?_, ?_⟩
    · apply (D_spec _).mpr
      left
      constructor <;> rfl
    · intro ι X S w
      constructor
      · rintro ⟨hleaf, ⟨a, ha, hα⟩, ⟨b, hb, hβ⟩⟩
        change readout w (block (X a)) = .alpha at hα
        change readout w (block (X b)) = .beta at hβ
        have hab : X a ≠ X b := by intro h; rw [h, hβ] at hα; cases hα
        have hno (i : ι) (hi : i ∈ S) : X i ≠ .a := by
          intro hia
          have hli := hleaf i hi
          change readout w (block (X i)) = .alpha ∨ readout w (block (X i)) = .beta at hli
          rw [hia] at hli
          by_cases haa : X a = .a
          · have hba : X b ≠ .a := by intro hba; exact hab (haa.trans hba.symm)
            exact incompatible (X b) hba w hli (Or.inr hβ)
          · exact incompatible (X a) haa w hli (Or.inl hα)
        have hXa := hno a ha
        have hXb := hno b hb
        cases hxa : X a <;> cases hxb : X b
        all_goals try exact False.elim (hXa hxa)
        all_goals try exact False.elim (hXb hxb)
        all_goals try exact False.elim (hab (hxa.trans hxb.symm))
        · refine ⟨⟨hno, ⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩, (D_spec w).mpr (Or.inl ?_)⟩
          exact ⟨by simpa [hxa] using hα, by simpa [hxb] using hβ⟩
        · refine ⟨⟨hno, ⟨b, hb, hxb⟩, ⟨a, ha, hxa⟩⟩, (D_spec w).mpr (Or.inr ?_)⟩
          exact ⟨by simpa [hxb] using hβ, by simpa [hxa] using hα⟩
      · rintro ⟨⟨hno, ⟨u, hu, hXu⟩, ⟨v, hv, hXv⟩⟩, hw⟩
        rcases (D_spec w).mp hw with ⟨hα, hβ⟩ | ⟨hβ, hα⟩
        · refine ⟨?_, ⟨u, hu, by simpa [hXu] using hα⟩,
            ⟨v, hv, by simpa [hXv] using hβ⟩⟩
          intro i hi
          have hni := hno i hi
          cases hXi : X i <;> simp_all
        · refine ⟨?_, ⟨v, hv, by simpa [hXv] using hα⟩,
            ⟨u, hu, by simpa [hXu] using hβ⟩⟩
          intro i hi
          have hni := hno i hi
          cases hXi : X i <;> simp_all

  have row_facts {m : ℕ} (K : Finset (Finset (Fin m))) (i : Fin m) :
      letI : Fintype (FaceColumn K) := Fintype.ofFinite _
      letI : Fintype (PaddingColumn K) :=
        inferInstance
      letI : Fintype (Column K) :=
        inferInstance
      (∑ c : Column K, if entry i c = .a then 0 else 1) = M K := by
    classical
    letI : Fintype (FaceColumn K) := Fintype.ofFinite _
    letI : Fintype (PaddingColumn K) := inferInstance
    letI : Fintype (Column K) := inferInstance
    have face_count : (∑ c : FaceColumn K, if faceEntry i c = .a then 0 else 1) =
        rowCount K i := by
      have hv (c : FaceColumn K) : (if faceEntry i c = .a then 0 else 1) =
          if i ∈ c.val.1 then 1 else 0 := by
        by_cases hi : i ∈ c.val.1
        · simp [hi, (face_non_a i c).mpr hi]
        · have h : faceEntry i c = .a := by
            by_contra h
            exact hi ((face_non_a i c).mp h)
          simp [hi, h]
      simp_rw [hv]
      simp [rowCount, Finset.sum_filter]
    have padding_count :
        (∑ c : PaddingColumn K, if entry i (.inr c) = .a then 0 else 1) =
        M K - rowCount K i := by
      change (∑ c : (Σ j : Fin m, Fin (M K - rowCount K j)),
        if (if i = c.1 then Block.u else Block.a) = .a then 0 else 1) = _
      rw [Fintype.sum_sigma]
      have hv (j : Fin m) :
          (if (if i = j then Block.u else Block.a) = .a then 0 else 1) =
          if i = j then 1 else 0 := by by_cases h : i = j <;> simp [h]
      simp_rw [hv]
      simp [eq_comm]
    change (∑ c : FaceColumn K ⊕ PaddingColumn K, if entry i c = .a then 0 else 1) = _
    rw [Fintype.sum_sum_type]
    change (∑ c : FaceColumn K, if faceEntry i c = .a then 0 else 1) +
      (∑ c : PaddingColumn K, if entry i (.inr c) = .a then 0 else 1) = _
    rw [face_count, padding_count, Nat.add_sub_of_le]
    exact Finset.le_sup (Finset.mem_univ i)

  have context_prefix (n : ℕ) (w : Address) :
      locate n w = none ↔ ∃ j : Fin (n + 1), ∃ r : Address,
        r ≠ [] ∧ hole n j = w ++ r := by
    induction n generalizing w with
    | zero =>
      constructor
      · simp [locate]
      · rintro ⟨j, r, hr, hp⟩
        have hlength := congrArg List.length hp
        simp only [hole, List.length_nil, List.length_append] at hlength
        have hrnil : r = [] := by simpa using (show r.length = 0 by omega)
        exact False.elim (hr hrnil)
    | succ n hn =>
      cases w with
      | nil =>
        constructor
        · intro _
          exact ⟨0, [false], by simp, rfl⟩
        · intro _
          rfl
      | cons b w =>
        cases b with
        | false =>
          constructor
          · simp [locate]
          · rintro ⟨j, r, hr, hp⟩
            revert hp
            refine Fin.cases ?_ (fun k => ?_) j
            · intro hp
              have hlength := congrArg List.length hp
              simp only [hole, Fin.cases_zero, List.length_cons, List.length_nil,
                List.length_append] at hlength
              have hrnil : r = [] := by simpa using (show r.length = 0 by omega)
              exact False.elim (hr hrnil)
            · intro hp
              simp [hole] at hp
        | true =>
          constructor
          · intro h
            have htail : locate n w = none := by simpa [locate] using h
            obtain ⟨j, r, hr, hp⟩ := (hn w).mp htail
            exact ⟨j.succ, r, hr, by simpa [hole] using congrArg (List.cons true) hp⟩
          · rintro ⟨j, r, hr, hp⟩
            have htail : locate n w = none := by
              apply (hn w).mpr
              revert hp
              refine Fin.cases ?_ (fun k => ?_) j
              · intro hp
                simp [hole] at hp
              · intro hp
                exact ⟨k, r, hr, by simpa [hole] using hp⟩
            simp [locate, htail]
  have delta_comb {ι : Type} (n : ℕ) (X : ι → Fin (n + 1) → Block)
      (S : Finset ι) (w : Address) :
      w ∈ Delta (fun i => B_T n (fun j => block (X i j))) S ↔
        ∃ j v, w = hole n j ++ v ∧ Mixed (fun i => X i j) S ∧ v ∈ D := by
    cases hl : locate n w with
    | none =>
      constructor
      · rintro ⟨_, ⟨i, hi, ha⟩, _⟩
        change readout w (B_T n (fun j => block (X i j))) = .alpha at ha
        rw [address_facts.1, hl] at ha
        cases ha
      · rintro ⟨j, v, rfl, _, _⟩
        rw [address_facts.2.1] at hl
        cases hl
    | some p =>
      obtain ⟨j, v⟩ := p
      have hw := (address_facts.2.2 n w j v).mp hl
      have hdelta : w ∈ Delta (fun i => B_T n (fun j => block (X i j))) S ↔
          v ∈ Delta (fun i => block (X i j)) S := by
        unfold Delta
        simp only [Set.mem_setOf_eq]
        simp_rw [address_facts.1, hl]
      rw [hdelta, block_facts.2]
      constructor
      · rintro ⟨hX, hv⟩
        exact ⟨j, v, hw, hX, hv⟩
      · rintro ⟨k, u, hwu, hX, hu⟩
        have he := hl.symm.trans ((address_facts.2.2 n w k u).mpr hwu)
        have hp := Option.some.inj he
        have hk := congrArg Prod.fst hp
        have huv := congrArg Prod.snd hp
        change j = k at hk
        change v = u at huv
        subst k
        subst u
        exact ⟨hX, hu⟩
  have substitution_comb (n : ℕ) (X : Fin (n + 1) → Source) :
      substitution^[3] (B_T n X) = B_T n (fun j => substitution^[3] (X j)) := by
    induction n with
    | zero => rfl
    | succ n hn =>
      change FreeMagma.mul (substitution^[3] (X 0))
        (substitution^[3] (B_T n (fun j => X j.succ))) =
        FreeMagma.mul (substitution^[3] (X 0))
          (B_T n (fun j => substitution^[3] (X j.succ)))
      rw [hn]
  have pre_composition (b : Block) :
      composition (preimage b) = (1 + (if b = .a then 0 else 1), if b = .a then 0 else 1) := by
    cases b <;> simp [preimage, composition]
  have block_composition (b : Block) :
      composition (block b) =
        (1 + 3 * (if b = .a then 0 else 1), 2 + 5 * (if b = .a then 0 else 1)) := by
    cases b <;> simp [ActualImageSevenLeafSeparation.thirdImage, preimage,
      Function.iterate_succ_apply', substitution, composition]
  refine ⟨address_facts.1, context_prefix, ?_, ?_, ?_⟩
  · intro m n X S w
    exact delta_comb n X S w
  · intro n j k v u he
    have h := congrArg (locate n) he
    rw [address_facts.2.1, address_facts.2.1] at h
    exact Prod.mk.inj (Option.some.inj h)
  · intro m hm K hK hsingle
    classical
    letI : Fintype (FaceColumn K) := Fintype.ofFinite _
    letI : Fintype (PaddingColumn K) := inferInstance
    letI : Fintype (Column K) := inferInstance
    obtain ⟨F, hF, h0F⟩ := maximal_contains K {⟨0, by omega⟩} (hsingle ⟨0, by omega⟩)
    let c0 : FaceColumn K := ⟨(F, ⟨0, by omega⟩), hF, h0F (by simp)⟩
    letI : Nonempty (Column K) := ⟨.inl c0⟩
    let T := Nat.card (Column K)
    have hcard : T = Fintype.card (Column K) := Nat.card_eq_fintype_card
    have hT : 1 ≤ T := by rw [hcard]; exact Fintype.card_pos
    let n := T - 1
    have hsize : n + 1 = T := by omega
    refine ⟨hT, ?_⟩
    intro e
    let Q : Fin m → Source := fun i => B_T n (fun j => preimage (entry i (e j)))
    let P : Fin m → Source := fun i => B_T n (fun j => block (entry i (e j)))
    have hPQ (i : Fin m) : substitution^[3] (Q i) = P i := substitution_comb _ _
    have count (i : Fin m) : (∑ j : Fin (n + 1), if entry i (e j) = .a then 0 else 1) = M K := by
      exact (e.sum_comp (fun c => if entry i c = .a then (0 : ℕ) else 1)).trans (row_facts K i)
    have hQc (i : Fin m) : composition (Q i) = (T + M K, M K) := by
      rw [composition_comb]
      simp_rw [pre_composition]
      apply Prod.ext <;>
        simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib, count, hsize]
    have hPc (i : Fin m) : composition (P i) = (T + 3 * M K, 2 * T + 5 * M K) := by
      rw [composition_comb]
      simp_rw [block_composition]
      apply Prod.ext
      · rw [Prod.fst_sum]
        change Finset.sum Finset.univ (fun j : Fin (n + 1) => 1 + 3 * (if entry i (e j) = .a then 0 else 1)) = T + 3 * M K
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, count]
        simp [hsize]
      · rw [Prod.snd_sum]
        change Finset.sum Finset.univ (fun j : Fin (n + 1) => 2 + 5 * (if entry i (e j) = .a then 0 else 1)) = 2 * T + 5 * M K
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, count]
        simp [hsize, Nat.mul_comm]
    have hP_inj : Function.Injective P := by
      intro i j hij
      by_contra hne
      obtain ⟨F, hF, hiF⟩ := maximal_contains K {i} (hsingle i)
      let c : FaceColumn K := ⟨(F, i), hF, hiF (by simp)⟩
      let k := e.symm (.inl c)
      let w := hole n k ++ [false, true, false, true]
      have hr (r : Fin m) : readout w (P r) =
          readout [false, true, false, true] (block (entry r (.inl c))) := by
        change readout w (B_T n (fun k => block (entry r (e k)))) = _
        rw [address_facts.1]
        simp [w, address_facts.2.1, k]
      have h := congrArg (fun t => readout w t) hij
      rw [hr i, hr j] at h
      have hji : j ≠ i := Ne.symm hne
      by_cases hjF : j ∈ F <;>
        simp [entry, faceEntry, c, hji, hjF, ActualImageSevenLeafSeparation.thirdImage, preimage,
          Function.iterate_succ_apply', substitution, readout] at h
    have hQ_inj : Function.Injective Q := by
      intro i j hij
      apply hP_inj
      rw [← hPQ i, ← hPQ j, hij]
    refine ⟨hQ_inj, hP_inj, ?_, ?_, ?_⟩
    · intro i
      refine ⟨hPQ i, ⟨Q i, hPQ i⟩, hQc i, hPc i, ?_⟩
      rw [hPc i]
      dsimp only
      omega
    · intro i R
      constructor
      · intro hR
        exact ((SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
          ⟨fun s t => substitution.map_mul s t, fun t => rfl⟩).iterate 3)
          (hR.trans (hPQ i).symm)
      · rintro rfl
        exact hPQ i
    · intro S hS
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨j, v, _, hmix, _⟩ := (delta_comb n (fun i j => entry i (e j)) S w).mp hw
        exact (face_facts m hm K hK hsingle S hS).mp ⟨e j, hmix⟩
      · intro hSK
        obtain ⟨c, hmix⟩ := (face_facts m hm K hK hsingle S hS).mpr hSK
        refine ⟨hole n (e.symm c) ++ [false, true, false, true], ?_⟩
        apply (delta_comb n (fun i j => entry i (e j)) S _).mpr
        refine ⟨e.symm c, [false, true, false, true], rfl, ?_, block_facts.1⟩
        simpa using hmix

end D5.S3.Arith.FibonacciAtomic.FiniteHereditaryPatternRealization
