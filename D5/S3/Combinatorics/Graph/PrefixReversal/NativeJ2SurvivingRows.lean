/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingRows
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual reflected and positive short-row chains avoid all selected cuts. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingCircles
set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open Equiv Fin.NatCast
open D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent

open private contactAnchor_val from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open private first_a_cut second_a_cut from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels

open private surviving_adj_iff from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel

open private j2Contact j2_rotate_val j2_word1_initial_reflected j2_word0_contact_reflected j2_word2_initial_positive j2_word3_initial_reflected from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingSeams

open private j2_edge_generator_unique j2_h_contact_index j2_h_cut_domain j2_h_gap_star j2_h_lower_domain j2_h_lower_deleted j2_h_newgap_domain j2_h_newgap_deleted scanl_chain_cons from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingCircles

private theorem j2_rotation_b_predecessor {m : ℕ} (z : Configuration m)
    (r : ℕ) (hr : 1 ≤ r) :
    z * finRotate (m + 1) ^ r * b m =
      z * finRotate (m + 1) ^ (r - 1) * a m := by
  have hb : b m * b m = 1 := by
    apply Equiv.ext
    intro i
    exact PrefixReversalTripleOddNonGeneration.reverseIndex_involutive
      (L := m) (by omega) i
  have hRb : finRotate (m + 1) * b m = a m := by
    rw [← ab_eq_rotate, mul_assoc, hb, mul_one]
  calc
    _ = z * (finRotate (m + 1) ^ (r - 1) * finRotate (m + 1)) * b m := by
      rw [← pow_succ, show r - 1 + 1 = r by omega]
    _ = z * finRotate (m + 1) ^ (r - 1) * (finRotate (m + 1) * b m) := by
      simp only [mul_assoc]
    _ = _ := by rw [hRb]

private theorem j2_reflected_u_chain {m : ℕ} (z : Configuration m) (k r : ℕ)
    (hkr : k ≤ r)
    (ha : ∀ q, r - k ≤ q → q ≤ r → (survivingGraph m).Adj
      (z * finRotate (m + 1) ^ q * a m) (z * finRotate (m + 1) ^ q))
    (hb : ∀ q, r - k < q → q ≤ r → (survivingGraph m).Adj
      (z * finRotate (m + 1) ^ q) (z * finRotate (m + 1) ^ (q - 1) * a m)) :
    (List.scanl (· * ·) (z * finRotate (m + 1) ^ r * a m)
      (uWord m k)).IsChain (survivingGraph m).Adj := by
  induction k generalizing r with
  | zero =>
    apply scanl_chain_cons
    · simpa only [mul_assoc, a_sq, mul_one] using ha r (by omega) (by omega)
    · simp
  | succ k ih =>
    have hfirst : (z * finRotate (m + 1) ^ r * a m) * a m =
        z * finRotate (m + 1) ^ r := by simp only [mul_assoc, a_sq, mul_one]
    change (List.scanl (· * ·) (z * finRotate (m + 1) ^ r * a m)
      (a m :: b m :: uWord m k)).IsChain _
    apply scanl_chain_cons
    · simpa only [hfirst] using ha r (by omega) (by omega)
    · rw [hfirst]
      apply scanl_chain_cons
      · rw [j2_rotation_b_predecessor z r (by omega)]
        exact hb r (by omega) (by omega)
      · rw [j2_rotation_b_predecessor z r (by omega)]
        apply ih (r - 1) (by omega)
        · intro q hq hq'
          exact ha q (by omega) (by omega)
        · intro q hq hq'
          exact hb q (by omega) (by omega)

private theorem j2_reflected_ab_chain {m : ℕ} (z : Configuration m) (k r : ℕ)
    (hkr : k ≤ r)
    (ha : ∀ q, r - k < q → q ≤ r → (survivingGraph m).Adj
      (z * finRotate (m + 1) ^ q * a m) (z * finRotate (m + 1) ^ q))
    (hb : ∀ q, r - k < q → q ≤ r → (survivingGraph m).Adj
      (z * finRotate (m + 1) ^ q) (z * finRotate (m + 1) ^ (q - 1) * a m)) :
    (List.scanl (· * ·) (z * finRotate (m + 1) ^ r * a m)
      (List.replicate k [a m, b m]).flatten).IsChain (survivingGraph m).Adj := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
    have hfirst : (z * finRotate (m + 1) ^ r * a m) * a m =
        z * finRotate (m + 1) ^ r := by simp only [mul_assoc, a_sq, mul_one]
    rw [List.replicate_succ, List.flatten_cons]
    change (List.scanl (· * ·) (z * finRotate (m + 1) ^ r * a m)
      (a m :: b m :: (List.replicate k [a m, b m]).flatten)).IsChain _
    apply scanl_chain_cons
    · simpa only [hfirst] using ha r (by omega) (by omega)
    · rw [hfirst]
      apply scanl_chain_cons
      · rw [j2_rotation_b_predecessor z r (by omega)]
        exact hb r (by omega) (by omega)
      · rw [j2_rotation_b_predecessor z r (by omega)]
        apply ih (r - 1) (by omega)
        · intro q hq hq'
          exact ha q (by omega) (by omega)
        · intro q hq hq'
          exact hb q (by omega) (by omega)

/-- Actual b edges within one full circle are injectively labelled by the
positive rotation. Equality of undirected edges forces equality of their
terminal labels because b fixes the last position. -/
private theorem j2_positive_b_edge_injective {m : ℕ} (z : Configuration m) :
    Function.Injective (fun r : Fin (m + 1) =>
      s(z * finCycle r, z * finCycle r * b m)) := by
  intro r t he
  have hlast : (z * finCycle r) (Fin.last m) =
      (z * finCycle t) (Fin.last m) := by
    rcases Sym2.eq_iff.mp he with ⟨hx, _⟩ | ⟨hx, _⟩
    · exact congrArg (fun x : Configuration m => x (Fin.last m)) hx
    · have hv := congrArg (fun x : Configuration m => x (Fin.last m)) hx
      simpa only [Equiv.Perm.mul_apply, b_last] using hv
  simp only [Equiv.Perm.mul_apply, finCycle_apply] at hlast
  exact add_left_cancel (z.injective hlast)

private theorem j2_a_not_marked {m : ℕ} (hm : 5 ≤ m) (x : Configuration m) :
    ¬ MarkedCut m s(x, x * a m) := by
  rintro ⟨p, he⟩
  rw [native_j2_marked_edge] at he
  have hab : a m = b m := j2_edge_generator_unique _ _ _ _ (a_sq m) he
  have hv := congrArg (fun f : Configuration m => (f (Fin.last m)).val) hab
  simp only [a_apply, Fin.val_rev, Fin.val_last, Nat.sub_self, b_last] at hv
  omega

private theorem j2_b_not_marked_of_last {m : ℕ} (hm : 5 ≤ m) (x : Configuration m)
    (hv : (x (Fin.last m)).val ≠ m - 1) : ¬ MarkedCut m s(x, x * b m) := by
  rintro ⟨p, he⟩
  have hmem : x ∈ markedEdge m p := he ▸ Sym2.mem_mk_left _ _
  change x ∈ s(port m (p.1, p.2, false), port m (p.1, p.2, true)) at hmem
  rcases Sym2.mem_iff.mp hmem with hx | hx
  · apply hv
    rw [hx]
    exact native_j2_port_last hm (p.1, p.2, false)
  · apply hv
    rw [hx]
    exact native_j2_port_last hm (p.1, p.2, true)

private theorem j2_native_survives {m : ℕ} (hm : 5 ≤ m)
    (x g : Configuration m) (hd : F2Domain m x) (hg : g = a m ∨ g = b m)
    (hc : ¬ F2DeletedEdge m s(x, x * g)) (hv : ¬ MarkedCut m s(x, x * g)) :
    (survivingGraph m).Adj x (x * g) := by
  have hg1 : g ≠ 1 := by
    rcases hg with rfl | rfl
    · intro he
      have h := congrArg (fun f : Configuration m => (f ⟨0, by omega⟩).val) he
      simp only [a_apply, Fin.val_rev, Fin.val_mk, Equiv.Perm.one_apply] at h
      omega
    · intro he
      have h := congrArg (fun f : Configuration m => (f ⟨0, by omega⟩).val) he
      simp only [b_apply, Fin.val_mk, if_pos (by omega : 0 < m),
        Nat.sub_zero, Equiv.Perm.one_apply] at h
      omega
  apply (surviving_adj_iff m x (x * g)).mpr
  refine ⟨⟨Or.inl ⟨?_, hc⟩, hv⟩, ?_⟩
  · exact (native_f2_native_edge_catalog (by omega : 4 ≤ m) _).mpr
      ⟨x, g, hd, hg, rfl⟩
  · intro he
    exact hg1 (mul_left_cancel (by simpa only [mul_one] using he.symm))

private theorem j2_b_survives_of_terminal {m : ℕ} (hm : 5 ≤ m)
    (x : Configuration m) (hd : F2Domain m x)
    (h0 : (x (Fin.last m)).val ≠ 0) (hM : (x (Fin.last m)).val ≠ m)
    (hV : (x (Fin.last m)).val ≠ m - 1) :
    (survivingGraph m).Adj x (x * b m) := by
  apply j2_native_survives hm x (b m) hd (Or.inr rfl)
  · intro hc
    rcases (native_f2_b_cut_classification (by omega : 4 ≤ m) x).mp hc with
      ⟨j, _, hj⟩ | ⟨j, _, hj⟩ | ⟨j, _, hj⟩
    · exact h0 (congrArg Fin.val hj)
    · exact hM (congrArg Fin.val hj)
    · exact h0 (congrArg Fin.val hj)
  · exact j2_b_not_marked_of_last hm x hV

private theorem j2_core_a_anchors_in_lower {m : ℕ} (hm : 5 ≤ m) :
    SupplierStar (a m * c m) (1 : Configuration m) ∧
      SupplierStar (a m * c m) (Equiv.swap (0 : Fin (m + 1)) (Fin.last m)) := by
  constructor
  · apply (native_star_circle_partition (by omega : 3 ≤ m) (a m * c m) _).mpr
    refine ⟨⟨m - 1, by omega⟩, ?_⟩
    apply (native_cut_circle_iff (by omega : 4 ≤ m) (.inl ⟨m - 1, by omega⟩) _).mp
    rw [(first_a_cut (by omega : 4 ≤ m)).1]
    exact Or.inl rfl
  · apply (native_star_circle_partition (by omega : 3 ≤ m) (a m * c m) _).mpr
    refine ⟨⟨m - 2, by omega⟩, ?_⟩
    apply (native_cut_circle_iff (by omega : 4 ≤ m) (.inl ⟨m - 2, by omega⟩) _).mp
    rw [(second_a_cut (by omega : 4 ≤ m)).1]
    exact Or.inl rfl

/-- All a edges in a contact supplier avoid both core a cuts, including
its gap-zero contact circle where there are two separate F2 b cuts. -/
private theorem j2_contact_a_uncut {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (i : Fin m) (x : Configuration m)
    (hx : Circle (gapAnchor (contactAnchor j) i) x) :
    ¬ F2DeletedEdge m s(x, x * a m) := by
  intro hc
  have hn : NativeCircleEdge (gapAnchor (contactAnchor j) i) s(x, x * a m) :=
    ⟨x, a m, hx, Or.inl rfl, rfl⟩
  rcases (native_f2_a_cut_classification (by omega : 4 ≤ m) x).mp hc with he | he
  · have hv := native_circle_edge_endpoint _ (1 : Configuration m) _ hn
      (he ▸ Sym2.mem_mk_left _ _)
    exact Set.disjoint_left.mp (contact_star_lower_disjoint (by omega : 4 ≤ m) j)
      (j2_h_gap_star hm j i _ hv) (j2_core_a_anchors_in_lower hm).1
  · have hv := native_circle_edge_endpoint _
      (Equiv.swap (0 : Fin (m + 1)) (Fin.last m)) _ hn
      (he ▸ Sym2.mem_mk_left _ _)
    exact Set.disjoint_left.mp (contact_star_lower_disjoint (by omega : 4 ≤ m) j)
      (j2_h_gap_star hm j i _ hv) (j2_core_a_anchors_in_lower hm).2

private theorem j2_final_contact_positive_last {m : ℕ} (hm : 5 ≤ m)
    (q : ℕ) (hq : 1 ≤ q) (hq' : q ≤ m - 2) :
    ((contactAnchor (j2Contact hm) * finRotate (m + 1) ^ q) (Fin.last m)).val = q := by
  simp only [Equiv.Perm.mul_apply, contactAnchor_val, j2_rotate_val, Fin.val_last,
    j2Contact, Fin.val_mk]
  have hmod : (m + q) % (m + 1) = q - 1 := by
    rw [show m + q = (q - 1) + (m + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : q - 1 < m + 1)]
  rw [hmod, if_pos (by omega : q - 1 < m - 3 + 1)]
  omega

/-- The middle short U segment in word zero is now an actual scanl chain
in the SAME six-marked-cut graph, avoiding both of its owner C's F2 cuts. -/
private theorem j2_word0_contact_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (c m) (uWord m (m - 2))).IsChain (survivingGraph m).Adj := by
  rw [j2_word0_contact_reflected hm]
  apply j2_reflected_u_chain _ (m - 2) (m - 2) (by omega)
  · intro q hq hq'
    let x := contactAnchor (j2Contact hm) * finRotate (m + 1) ^ q * a m
    have hx : Circle (contactAnchor (j2Contact hm)) x := by
      right
      simp only [x, native_configurationCycle_reversal]
      rw [rotate_pow_eq_cycle, native_configurationCycle_rotation]
    have hx' : Circle
        (gapAnchor (contactAnchor (j2_h_contact_index hm)) ⟨0, by omega⟩) x := by
      simpa only [gapAnchor, Fin.val_mk, pow_zero, mul_one, j2_h_contact_index, j2Contact] using hx
    have hadj := j2_native_survives hm x (a m) (j2_h_newgap_domain hm _ x hx')
      (Or.inl rfl) (j2_contact_a_uncut hm _ _ x hx') (j2_a_not_marked hm x)
    simpa only [x, mul_assoc, a_sq, mul_one] using hadj
  · intro q hq hq'
    let x := contactAnchor (j2Contact hm) * finRotate (m + 1) ^ q
    have hx : Circle (contactAnchor (j2Contact hm)) x := by
      left
      dsimp only [x]
      rw [rotate_pow_eq_cycle, native_configurationCycle_rotation]
    have hx' : Circle
        (gapAnchor (contactAnchor (j2_h_contact_index hm)) ⟨0, by omega⟩) x := by
      simpa only [gapAnchor, Fin.val_mk, pow_zero, mul_one, j2_h_contact_index, j2Contact] using hx
    have hlast : (x (Fin.last m)).val = q :=
      j2_final_contact_positive_last hm q (by omega) hq'
    have hadj := j2_b_survives_of_terminal hm x (j2_h_newgap_domain hm _ x hx')
      (by omega) (by omega) (by omega)
    simpa only [x,
      j2_rotation_b_predecessor (contactAnchor (j2Contact hm)) q (by omega)] using hadj

private theorem j2_b_reflected (m : ℕ) (z : Configuration m) :
    z * b m = z * finRotate (m + 1) ^ m * a m := by
  have hr : (m : Fin (m + 1)) = -1 := by
    rw [show (m : Fin (m + 1)) = Fin.last m by apply Fin.ext; simp,
      ← Fin.neg_last m, neg_neg]
  rw [b_eq_cycle_a, rotate_pow_eq_cycle, hr, mul_assoc]

private theorem j2_b_single_cut_survives {m : ℕ} (hm : 5 ≤ m)
    (z x : Configuration m) (hx : Circle z x) (hd : F2Domain m x)
    (hdeleted : ∀ e, NativeCircleEdge z e → F2DeletedEdge m e → e = s(z, z * b m))
    (h0 : (x (Fin.last m)).val ≠ (z (Fin.last m)).val)
    (hV : (x (Fin.last m)).val ≠ m - 1) :
    (survivingGraph m).Adj x (x * b m) := by
  apply j2_native_survives hm x (b m) hd (Or.inr rfl)
  · intro hc
    have he := hdeleted _ ⟨x, b m, hx, Or.inr rfl, rfl⟩ hc
    have hlast : x (Fin.last m) = z (Fin.last m) := by
      rcases Sym2.eq_iff.mp he with ⟨hxz, _⟩ | ⟨hxz, _⟩
      · exact congrArg (fun f : Configuration m => f (Fin.last m)) hxz
      · have h := congrArg (fun f : Configuration m => f (Fin.last m)) hxz
        simpa only [Equiv.Perm.mul_apply, b_last] using h
    exact h0 (congrArg Fin.val hlast)
  · exact j2_b_not_marked_of_last hm x hV

private theorem j2_b_complement_short_chain {m : ℕ} (hm : 5 ≤ m)
    (z : Configuration m) (k : ℕ) (hk : k ≤ m)
    (hdomain : ∀ x, Circle z x → F2Domain m x)
    (ha : ∀ x, Circle z x → ¬ F2DeletedEdge m s(x, x * a m))
    (hb : ∀ e, NativeCircleEdge z e → F2DeletedEdge m e → e = s(z, z * b m))
    (hlast : ∀ q, m - k < q → q ≤ m →
      ((z * finRotate (m + 1) ^ q) (Fin.last m)).val ≠ (z (Fin.last m)).val ∧
      ((z * finRotate (m + 1) ^ q) (Fin.last m)).val ≠ m - 1) :
    (List.scanl (· * ·) (z * b m) (uWord m k)).IsChain (survivingGraph m).Adj := by
  rw [j2_b_reflected]
  apply j2_reflected_u_chain _ k m hk
  · intro q hq hq'
    let x := z * finRotate (m + 1) ^ q * a m
    have hx : Circle z x := by
      right
      simp only [x, native_configurationCycle_reversal]
      rw [rotate_pow_eq_cycle, native_configurationCycle_rotation]
    have hadj := j2_native_survives hm x (a m) (hdomain x hx) (Or.inl rfl)
      (ha x hx) (j2_a_not_marked hm x)
    simpa only [x, mul_assoc, a_sq, mul_one] using hadj
  · intro q hq hq'
    let x := z * finRotate (m + 1) ^ q
    have hx : Circle z x := by
      left
      dsimp only [x]
      rw [rotate_pow_eq_cycle, native_configurationCycle_rotation]
    have hadj := j2_b_single_cut_survives hm z x hx (hdomain x hx) hb
      (hlast q hq hq').1 (hlast q hq hq').2
    simpa only [x, j2_rotation_b_predecessor z q (by omega)] using hadj

private theorem j2_positive_last_position {m : ℕ} (q : ℕ)
    (hq : 1 ≤ q) (hq' : q ≤ m) :
    ((finRotate (m + 1) ^ q) (Fin.last m)).val = q - 1 := by
  rw [j2_rotate_val]
  simp only [Fin.val_last]
  rw [show m + q = (q - 1) + (m + 1) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega : q - 1 < m + 1)]

private theorem j2_gap_m1_positive_last {m : ℕ} (hm : 5 ≤ m)
    (q : ℕ) (hq : 2 ≤ q) (hq' : q ≤ m) :
    ((gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 1, by omega⟩ *
      finRotate (m + 1) ^ q) (Fin.last m)).val = if q = m then m else q - 1 := by
  simp only [Equiv.Perm.mul_apply, gapAnchor, contactAnchor_val,
    native_bc_pow_val (by omega : 2 ≤ m), j2_positive_last_position q (by omega) hq',
    Fin.val_mk, j2Contact]
  rw [if_pos (by omega : q - 1 < m)]
  have hmod : (q - 1 + (m - 1)) % m = q - 2 := by
    rw [show q - 1 + (m - 1) = (q - 2) + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : q - 2 < m)]
  rw [hmod]
  split_ifs <;> omega

private theorem j2_gap_m2_positive_last {m : ℕ} (hm : 5 ≤ m)
    (q : ℕ) (hq : 3 ≤ q) (hq' : q ≤ m) :
    ((gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩ *
      finRotate (m + 1) ^ q) (Fin.last m)).val = q - 2 := by
  simp only [Equiv.Perm.mul_apply, gapAnchor, contactAnchor_val,
    native_bc_pow_val (by omega : 2 ≤ m), j2_positive_last_position q (by omega) hq',
    Fin.val_mk, j2Contact]
  rw [if_pos (by omega : q - 1 < m)]
  have hmod : (q - 1 + (m - 2)) % m = q - 3 := by
    rw [show q - 1 + (m - 2) = (q - 3) + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : q - 3 < m)]
  rw [hmod, if_pos (by omega : q - 3 < m - 3 + 1)]
  omega

private theorem j2_contact_gap_last_zero {m : ℕ} (hm : 5 ≤ m) (i : Fin m) :
    (gapAnchor (contactAnchor (j2Contact hm)) i (Fin.last m)).val = 0 := by
  simp (disch := omega) only [gapAnchor, Equiv.Perm.mul_apply, contactAnchor_val,
    native_bc_pow_val (by omega : 2 ≤ m), Fin.val_last, j2Contact, Fin.val_mk,
    if_pos, if_neg]

private theorem j2_word0_final_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·)
      (gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 1, by omega⟩ * b m)
      (uWord m (m - 1))).IsChain (survivingGraph m).Adj := by
  apply j2_b_complement_short_chain hm _ _ (by omega)
  · exact j2_h_newgap_domain hm _
  · exact j2_contact_a_uncut hm _ _
  · exact j2_h_newgap_deleted hm _ (by simp only [Fin.val_mk]; omega)
  · intro q hq hq'
    rw [j2_gap_m1_positive_last hm q (by omega) hq', j2_contact_gap_last_zero hm]
    split_ifs <;> constructor <;> omega

private theorem j2_word3_final_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·)
      (gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩ * b m)
      (uWord m (m - 2))).IsChain (survivingGraph m).Adj := by
  apply j2_b_complement_short_chain hm _ _ (by omega)
  · exact j2_h_newgap_domain hm _
  · exact j2_contact_a_uncut hm _ _
  · exact j2_h_newgap_deleted hm _ (by simp only [Fin.val_mk]; omega)
  · intro q hq hq'
    rw [j2_gap_m2_positive_last hm q (by omega) hq', j2_contact_gap_last_zero hm]
    constructor <;> omega

private theorem j2_circle_native_closed {m : ℕ} (z x g : Configuration m)
    (hx : Circle z x) (hg : g = a m ∨ g = b m) : Circle z (x * g) := by
  exact native_circle_edge_endpoint z (x * g) s(x, x * g)
    ⟨x, g, hx, hg, rfl⟩ (Sym2.mem_mk_right _ _)

private theorem j2_lower_a_uncut {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (x : Configuration m) (hx : Circle (lowerPort j) x) :
    ¬ F2DeletedEdge m s(x, x * a m) := by
  intro hc
  have he := j2_h_lower_deleted hm j _ ⟨x, a m, hx, Or.inl rfl, rfl⟩ hc
  have hab : a m = b m := j2_edge_generator_unique _ _ _ _ (a_sq m) he
  have hv := congrArg (fun f : Configuration m => (f (Fin.last m)).val) hab
  simp only [a_apply, Fin.val_rev, Fin.val_last, Nat.sub_self, b_last] at hv
  omega

private theorem j2_lower_a_survives {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (x : Configuration m) (hx : Circle (lowerPort j) x) :
    (survivingGraph m).Adj x (x * a m) :=
  j2_native_survives hm x (a m) (j2_h_lower_domain hm j x hx) (Or.inl rfl)
    (j2_lower_a_uncut hm j x hx) (j2_a_not_marked hm x)

private theorem j2_final_contact_a_survives {m : ℕ} (hm : 5 ≤ m)
    (i : Fin m) (x : Configuration m)
    (hx : Circle (gapAnchor (contactAnchor (j2Contact hm)) i) x) :
    (survivingGraph m).Adj x (x * a m) :=
  j2_native_survives hm x (a m) (j2_h_newgap_domain hm i x hx) (Or.inl rfl)
    (j2_contact_a_uncut hm _ i x hx) (j2_a_not_marked hm x)

private theorem j2_lower_last_zero {m : ℕ} (hm : 5 ≤ m) (j : Fin (m - 2)) :
    ((lowerPort j) (Fin.last m)).val = 0 := by
  change ((a m * c m) (((b m * c m) ^ j.val) (Fin.last m))).val = 0
  rw [native_ac_apply_val (by omega : 3 ≤ m), native_bc_pow_val (by omega : 2 ≤ m)]
  simp (disch := omega) only [Fin.val_last, if_pos, if_neg, Nat.sub_self]

private theorem j2_final_lower_positive_last {m : ℕ} (hm : 5 ≤ m)
    (q : ℕ) (hq : 2 ≤ q) (hq' : q ≤ m) :
    ((lowerPort (j2Contact hm) * finRotate (m + 1) ^ q) (Fin.last m)).val =
      if q = 2 then m else q - 2 := by
  simp only [Equiv.Perm.mul_apply]
  simp only [native_lowerPort_val (by omega : 3 ≤ m) (j2Contact hm) _
    (by rw [j2_positive_last_position q (by omega) hq']; omega),
    j2_positive_last_position q (by omega) hq']
  simp only [j2Contact, Fin.val_mk]
  by_cases h2 : q = 2
  · have hmod : (q - 1 + (m - 3)) % m = m - 2 := by
      rw [show q - 1 + (m - 3) = m - 2 by omega,
        Nat.mod_eq_of_lt (by omega : m - 2 < m)]
    simp only [hmod, if_pos (by omega : m - 2 < m - 1), if_pos h2]
    omega
  · by_cases h3 : q = 3
    · have hmod : (q - 1 + (m - 3)) % m = m - 1 := by
        rw [show q - 1 + (m - 3) = m - 1 by omega,
          Nat.mod_eq_of_lt (by omega : m - 1 < m)]
      simp only [hmod, if_neg (by omega : ¬ m - 1 < m - 1), if_neg h2]
      omega
    · have hmod : (q - 1 + (m - 3)) % m = q - 4 := by
        rw [show q - 1 + (m - 3) = (q - 4) + m by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : q - 4 < m)]
      simp only [hmod, if_pos (by omega : q - 4 < m - 1), if_neg h2]
      omega

private theorem j2_word4_final_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (lowerPort (j2Contact hm) * b m)
      (uWord m (m - 1))).IsChain (survivingGraph m).Adj := by
  apply j2_b_complement_short_chain hm _ _ (by omega)
  · exact j2_h_lower_domain hm _
  · exact j2_lower_a_uncut hm _
  · exact j2_h_lower_deleted hm _
  · intro q hq hq'
    rw [j2_final_lower_positive_last hm q (by omega) hq', j2_lower_last_zero hm]
    split_ifs <;> constructor <;> omega

private theorem j2_word1_final_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (lowerPort (j2Contact hm)) [a m]).IsChain
      (survivingGraph m).Adj := by
  apply scanl_chain_cons
  · exact j2_lower_a_survives hm _ _ (Or.inl rfl)
  · simp

private theorem j2_word2_initial_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 2) [a m]).IsChain
      (survivingGraph m).Adj := by
  rw [j2_word2_initial_positive hm]
  apply scanl_chain_cons
  · apply j2_final_contact_a_survives hm ⟨0, by omega⟩
    simp only [gapAnchor, Fin.val_mk, pow_zero, mul_one]
    left
    rw [rotate_pow_eq_cycle, native_configurationCycle_rotation]
  · simp

private theorem j2_word3_initial_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 3) [a m]).IsChain
      (survivingGraph m).Adj := by
  rw [j2_word3_initial_reflected hm]
  apply scanl_chain_cons
  · apply j2_final_contact_a_survives hm ⟨m - 1, by omega⟩
    right
    exact native_configurationCycle_reversal _
  · simp

private theorem j2_gap_m2_reflected_last {m : ℕ} (hm : 5 ≤ m) :
    ((gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩ * a m)
      (Fin.last m)).val = m := by
  simp (disch := omega) only [Equiv.Perm.mul_apply, a_apply, Fin.rev_last,
    gapAnchor, contactAnchor_val, native_bc_pow_val (by omega : 2 ≤ m),
    Fin.val_zero, Fin.val_mk, j2Contact, if_pos, if_neg, Nat.zero_add,
    Nat.mod_eq_of_lt (by omega : m - 2 < m)]

private theorem j2_word2_final_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·)
      (gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩)
      [a m, b m, a m]).IsChain (survivingGraph m).Adj := by
  let z := gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩
  have hza : Circle z (z * a m) :=
    j2_circle_native_closed z z (a m) (Or.inl rfl) (Or.inl rfl)
  have hzab : Circle z (z * a m * b m) :=
    j2_circle_native_closed z (z * a m) (b m) hza (Or.inr rfl)
  change (List.scanl (· * ·) z [a m, b m, a m]).IsChain _
  apply scanl_chain_cons
  · exact j2_final_contact_a_survives hm _ z (Or.inl rfl)
  · apply scanl_chain_cons
    · apply j2_b_single_cut_survives hm z (z * a m) hza
        (j2_h_newgap_domain hm _ _ hza)
        (j2_h_newgap_deleted hm _ (by simp only [Fin.val_mk]; omega))
      · rw [show ((z * a m) (Fin.last m)).val = m from
          j2_gap_m2_reflected_last hm, show (z (Fin.last m)).val = 0 from
          j2_contact_gap_last_zero hm _]
        omega
      · rw [show ((z * a m) (Fin.last m)).val = m from
          j2_gap_m2_reflected_last hm]
        omega
    · apply scanl_chain_cons
      · exact j2_final_contact_a_survives hm _ _ hzab
      · simp


private theorem j2_circle_positive {m : ℕ} (z : Configuration m) (q : ℕ) :
    Circle z (z * finRotate (m + 1) ^ q) := by
  left
  rw [rotate_pow_eq_cycle]
  exact native_configurationCycle_rotation z _

private theorem j2_circle_reflected {m : ℕ} (z : Configuration m) (q : ℕ) :
    Circle z (z * finRotate (m + 1) ^ q * a m) := by
  right
  rw [native_configurationCycle_reversal, rotate_pow_eq_cycle,
    native_configurationCycle_rotation]

private theorem j2_t_lower_star {m : ℕ} (hm : 5 ≤ m) (i : Fin m)
    (x : Configuration m) (hx : Circle
      (NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2))) x) :
    SupplierStar (a m * c m) x := by
  apply (native_star_circle_partition (by omega : 3 ≤ m) (a m * c m) x).mpr
  refine ⟨i, ?_⟩
  exact (native_cut_circle_iff (by omega : 4 ≤ m) (.inl i) x).mp hx

private theorem j2_t_lower_cut_deleted {m : ℕ} (hm : 5 ≤ m) (i : Fin m)
    (e : Sym2 (Configuration m))
    (he : NativeCircleEdge
      (NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2))) e)
    (hd : F2DeletedEdge m e) :
    e = s(NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)),
      NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)) *
        cutGenerator (.inl i : Fin m ⊕ Fin (m - 2))) := by
  rcases hd with ⟨p, hp⟩ | ⟨j, k, hjk⟩
  · have hv := native_circle_edge_endpoint _ (NativeCoreSplicing.cutStart p) e he
      (hp ▸ Sym2.mem_mk_left _ _)
    have hip : (.inl i : Fin m ⊕ Fin (m - 2)) = p :=
      native_t_circle_owner_unique (by omega : 4 ≤ m) (NativeCoreSplicing.cutStart p)
        (.inl i) p ((native_cut_circle_iff (by omega : 4 ≤ m) (.inl i) _).mp hv)
        ((native_cut_circle_iff (by omega : 4 ≤ m) p _).mp (Or.inl rfl))
    simpa only [hip] using hp
  · have hv := native_circle_edge_endpoint _ (gapAnchor (contactAnchor j) k) e he
      (hjk ▸ Sym2.mem_mk_left _ _)
    exact (Set.disjoint_left.mp (contact_star_lower_disjoint (by omega : 4 ≤ m) j)
      (j2_h_gap_star hm j k _ (Or.inl rfl)) (j2_t_lower_star hm i _ hv)).elim

private theorem j2_positive_a_edge_injective {m : ℕ} (hm : 5 ≤ m)
    (z : Configuration m) : Function.Injective (fun r : Fin (m + 1) =>
      s(z * finCycle r, z * finCycle r * a m)) := by
  intro r t he
  rcases Sym2.eq_iff.mp he with ⟨hx, _⟩ | ⟨hx, _⟩
  · have hc : (circleEquiv (by omega : 3 ≤ m) z) (r, false) =
        (circleEquiv (by omega : 3 ≤ m) z) (t, false) := by
      apply Subtype.ext
      change circleCoordinate z (r, false) = circleCoordinate z (t, false)
      simpa only [circleCoordinate, Bool.false_eq_true, ↓reduceIte, mul_one] using hx
    exact congrArg Prod.fst ((circleEquiv (by omega : 3 ≤ m) z).injective hc)
  · have hc : (circleEquiv (by omega : 3 ≤ m) z) (r, false) =
        (circleEquiv (by omega : 3 ≤ m) z) (t, true) := by
      apply Subtype.ext
      change circleCoordinate z (r, false) = circleCoordinate z (t, true)
      simpa only [circleCoordinate, Bool.false_eq_true, ↓reduceIte, mul_one] using hx
    have hb : false = true :=
      congrArg Prod.snd ((circleEquiv (by omega : 3 ≤ m) z).injective hc)
    cases hb

private theorem j2_t_a_circle_b_survives {m : ℕ} (hm : 5 ≤ m) (i : Fin m)
    (hi : cutGenerator (.inl i : Fin m ⊕ Fin (m - 2)) = a m)
    (x : Configuration m)
    (hx : Circle (NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2))) x)
    (hV : (x (Fin.last m)).val ≠ m - 1) :
    (survivingGraph m).Adj x (x * b m) := by
  apply j2_native_survives hm x (b m) (Or.inl (j2_h_cut_domain hm (.inl i) x hx))
    (Or.inr rfl) _ (j2_b_not_marked_of_last hm x hV)
  intro hd
  have he := j2_t_lower_cut_deleted hm i _ ⟨x, b m, hx, Or.inr rfl, rfl⟩ hd
  rw [hi] at he
  have hb : b m * b m = 1 := by
    apply Equiv.ext
    intro q
    exact PrefixReversalTripleOddNonGeneration.reverseIndex_involutive
      (L := m) (by omega) q
  have hba := j2_edge_generator_unique _ _ _ _ hb he
  have hv := congrArg (fun f : Configuration m => (f (Fin.last m)).val) hba
  simp only [b_last, a_apply, Fin.val_rev, Fin.val_last, Nat.sub_self] at hv
  omega

private theorem j2_t_a_circle_a_survives {m : ℕ} (hm : 5 ≤ m) (i : Fin m)
    (hi : cutGenerator (.inl i : Fin m ⊕ Fin (m - 2)) = a m)
    (q : ℕ) (hq0 : 1 ≤ q) (hq : q ≤ m) :
    (survivingGraph m).Adj
      (NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)) * finRotate (m + 1) ^ q)
      (NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)) * finRotate (m + 1) ^ q * a m) := by
  let z := NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2))
  have hx := j2_circle_positive z q
  apply j2_native_survives hm _ (a m) (Or.inl (j2_h_cut_domain hm (.inl i) _ hx))
    (Or.inl rfl) _ (j2_a_not_marked hm _)
  intro hd
  have he := j2_t_lower_cut_deleted hm i _ ⟨_, a m, hx, Or.inl rfl, rfl⟩ hd
  rw [hi] at he
  have hcoord : (⟨q, by omega⟩ : Fin (m + 1)) = 0 := by
    apply j2_positive_a_edge_injective hm z
    have hqfin : (q : Fin (m + 1)) = ⟨q, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : q < m + 1), Fin.val_mk]
    simpa only [rotate_pow_eq_cycle, z, hqfin, cycle_zero, mul_one] using he
  have hval := congrArg Fin.val hcoord
  simp only [Fin.val_mk, Fin.val_zero] at hval
  omega

private theorem j2_word1_initial_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 1)
      (List.replicate (m - 1) [a m, b m]).flatten).IsChain (survivingGraph m).Adj := by
  rw [j2_word1_initial_reflected hm]
  change (List.scanl (· * ·) ((1 : Configuration m) * finRotate (m + 1) ^ (m - 1) * a m)
    (List.replicate (m - 1) [a m, b m]).flatten).IsChain _
  apply j2_reflected_ab_chain _ _ _ (le_refl _)
  · intro q hq0 hq
    have ha := j2_t_a_circle_a_survives hm ⟨m - 1, by omega⟩
      (first_a_cut (by omega : 4 ≤ m)).2 q (by omega) (by omega)
    simpa only [(first_a_cut (by omega : 4 ≤ m)).1, one_mul] using ha.symm
  · intro q hq0 hq
    have hb := j2_t_a_circle_b_survives hm ⟨m - 1, by omega⟩
      (first_a_cut (by omega : 4 ≤ m)).2 (finRotate (m + 1) ^ q)
      (by simpa only [(first_a_cut (by omega : 4 ≤ m)).1, one_mul] using j2_circle_positive 1 q)
      (by
        have hp := j2_positive_last_position q (by omega) (by omega : q ≤ m)
        change ((finRotate (m + 1) ^ q) (Fin.last m)).val ≠ m - 1
        rw [hp]
        omega)
    have hpred : finRotate (m + 1) ^ q * b m =
        finRotate (m + 1) ^ (q - 1) * a m := by
      simpa only [one_mul] using j2_rotation_b_predecessor (1 : Configuration m) q (by omega)
    simpa only [one_mul, hpred] using hb

private theorem j2_t_initial_ab_chain {m : ℕ} (hm : 5 ≤ m) (i : Fin m)
    (hi : cutGenerator (.inl i : Fin m ⊕ Fin (m - 2)) = a m)
    (hV : ((NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)))
      (Fin.last m)).val ≠ m - 1) :
    (List.scanl (· * ·)
      (NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)) * finRotate (m + 1) ^ m)
      [a m, b m]).IsChain (survivingGraph m).Adj := by
  let z := NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2))
  apply scanl_chain_cons
  · exact j2_t_a_circle_a_survives hm i hi m (by omega) (le_refl _)
  · apply scanl_chain_cons
    · apply j2_t_a_circle_b_survives hm i hi _ (j2_circle_reflected z m)
      have hpos : (finRotate (m + 1) ^ m) ((a m) (Fin.last m)) = Fin.last m := by
        apply Fin.ext
        simp only [a_apply, Fin.rev_last]
        rw [j2_rotate_val]
        simp only [Fin.val_zero, Fin.val_last, Nat.zero_add,
          Nat.mod_eq_of_lt (by omega : m < m + 1)]
      simpa only [Equiv.Perm.mul_apply, hpos, z] using hV
    · simp

private theorem j2_word0_initial_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 0) [a m, b m]).IsChain (survivingGraph m).Adj := by
  have h := j2_t_initial_ab_chain hm ⟨m - 1, by omega⟩ (first_a_cut (by omega : 4 ≤ m)).2
    (by simp only [(first_a_cut (by omega : 4 ≤ m)).1, Equiv.Perm.one_apply, Fin.val_last]; omega)
  simpa only [(first_a_cut (by omega : 4 ≤ m)).1, one_mul, wordStart, rightPort,
    Fin.val_zero] using h

private theorem j2_word4_initial_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 4) [a m, b m]).IsChain (survivingGraph m).Adj := by
  have h := j2_t_initial_ab_chain hm ⟨m - 2, by omega⟩ (second_a_cut (by omega : 4 ≤ m)).2
    (by simp only [(second_a_cut (by omega : 4 ≤ m)).1, Equiv.swap_apply_right, Fin.val_zero]; omega)
  simpa only [(second_a_cut (by omega : 4 ≤ m)).1, wordStart, bar, rightPort,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h




end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
