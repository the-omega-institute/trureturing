/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingEdges
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingEdges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual five surviving words consume the native rows and seam constructions. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingRows
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


open private actual_surviving_degree actual_port_leaf literal_trace_nonbacktracking literal_j2_letters from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel

open private j2Contact j2_h_product j2_b_cb_pow j2_word0_first_seed j2_word0_second_seed j2_word1_seed j2_word2_seed j2_word3_seed j2_word4_seed j2_word1_repeated_c j2_word2_repeated_c j2_word0_first_c j2_word0_second_c j2_word3_c j2_word4_c j2_word0_final_b_start j2_word3_final_b_start j2_word4_final_b_start j2_cb_c_pow j2_word1_final_a_start j2_word2_final_aba_start from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingSeams

open private j2_c_survives j2_h_contact_index j2_h_lower_survives j2_h_newgap_survives scanl_chain_cons from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingCircles

open private j2_word0_contact_chain j2_word0_final_chain j2_word3_final_chain j2_word4_final_chain j2_word1_final_chain j2_word2_initial_chain j2_word3_initial_chain j2_word2_final_chain j2_word1_initial_chain j2_word0_initial_chain j2_word4_initial_chain from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingRows

private theorem scanl_chain_append {m : ℕ} (G : SimpleGraph (Configuration m))
    (z : Configuration m) (l k : List (Configuration m))
    (hl : (List.scanl (· * ·) z l).IsChain G.Adj)
    (hk : (List.scanl (· * ·) (z * l.prod) k).IsChain G.Adj) :
    (List.scanl (· * ·) z (l ++ k)).IsChain G.Adj := by
  induction l generalizing z with
  | nil => simpa only [List.nil_append, List.prod_nil, mul_one] using hk
  | cons g l ih =>
    rw [List.scanl_cons, List.isChain_cons] at hl
    apply scanl_chain_cons
    · apply hl.1
      simp only [List.head?_scanl, Option.mem_some_iff]
    · apply ih _ hl.2
      simpa only [List.prod_cons, mul_assoc] using hk

private theorem repeated_ch_chain {m : ℕ} (z : Configuration m) (k : ℕ)
    (hc : ∀ t, t < k → (survivingGraph m).Adj
      (z * (c m * b m) ^ t) (z * (c m * b m) ^ t * c m))
    (hh : ∀ t, t < k →
      (List.scanl (· * ·) (z * (c m * b m) ^ t * c m)
        (uWord m m)).IsChain (survivingGraph m).Adj) :
    (List.scanl (· * ·) z
      (List.replicate k ([c m] ++ uWord m m)).flatten).IsChain
        (survivingGraph m).Adj := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    apply scanl_chain_append
    · exact ih (fun t ht => hc t (by omega)) (fun t ht => hh t (by omega))
    · have hp : ((List.replicate k ([c m] ++ uWord m m)).flatten).prod =
          (c m * b m) ^ k := by
        simp only [List.prod_flatten, List.map_replicate, List.prod_replicate,
          List.prod_append, List.prod_cons, List.prod_nil, mul_one, j2_h_product]
      rw [hp, List.singleton_append]
      exact scanl_chain_cons _ _ _ _ (hc k (by omega)) (hh k (by omega))

private theorem j2_word1_repeated_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (a m)
      (List.replicate (m - 3) ([c m] ++ uWord m m)).flatten).IsChain
        (survivingGraph m).Adj := by
  apply repeated_ch_chain
  · intro t ht
    exact j2_c_survives hm _ (j2_word1_repeated_c hm ⟨t, by omega⟩)
  · intro t ht
    let j : Fin (m - 2) := ⟨t, by omega⟩
    have he : a m * (c m * b m) ^ t * c m = lowerPort j := by
      rw [mul_assoc (a m), j2_cb_c_pow]
      simp only [lowerPort, j, Fin.val_mk, mul_assoc]
    rw [he]
    obtain ⟨w, _, _, hs, _⟩ := j2_h_lower_survives hm j ht
    rw [← hs]
    exact w.isChain_adj_support

private theorem j2_word2_repeated_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (contactAnchor (j2Contact hm) * b m)
      (List.replicate (m - 3) ([c m] ++ uWord m m)).flatten).IsChain
        (survivingGraph m).Adj := by
  apply repeated_ch_chain
  · intro t ht
    exact j2_c_survives hm _ (j2_word2_repeated_c hm ⟨t, by omega⟩)
  · intro t ht
    let i : Fin m := ⟨t + 1, by omega⟩
    have he : contactAnchor (j2Contact hm) * b m * (c m * b m) ^ t * c m =
        gapAnchor (contactAnchor (j2Contact hm)) i := by
      rw [mul_assoc (contactAnchor (j2Contact hm)), j2_b_cb_pow]
      simp only [gapAnchor, i, Fin.val_mk, pow_succ, mul_assoc]
    rw [he]
    obtain ⟨w, _, _, hs, _⟩ := j2_h_newgap_survives hm i (by simp only [i, Fin.val_mk]; omega)
      (by simp only [i, Fin.val_mk]; omega)
    have hw := w.isChain_adj_support
    rw [hs] at hw
    simpa only [j2_h_contact_index, j2Contact] using hw

private theorem scanl_chain_append_at {m : ℕ} (G : SimpleGraph (Configuration m))
    (z y : Configuration m) (l k : List (Configuration m))
    (hprod : z * l.prod = y)
    (hl : (List.scanl (· * ·) z l).IsChain G.Adj)
    (hk : (List.scanl (· * ·) y k).IsChain G.Adj) :
    (List.scanl (· * ·) z (l ++ k)).IsChain G.Adj := by
  apply scanl_chain_append G z l k hl
  rw [hprod]
  exact hk

private theorem j2_repeated_ch_product (m k : ℕ) :
    ((List.replicate k ([c m] ++ uWord m m)).flatten).prod =
      (c m * b m) ^ k := by
  simp only [List.prod_flatten, List.map_replicate, List.prod_replicate,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one, j2_h_product]

private theorem j2_word0_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 0) (word m 0)).IsChain
      (survivingGraph m).Adj := by
  have hContact : c m * (uWord m (m - 2)).prod = contactAnchor (j2Contact hm) := by
    have h := j2_word0_second_seed hm
    rw [j2_word0_first_seed hm, one_mul] at h
    exact h
  have hfinal : (List.scanl (· * ·) (contactAnchor (j2Contact hm))
      (c m :: uWord m (m - 1))).IsChain (survivingGraph m).Adj := by
    apply scanl_chain_cons
    · exact j2_c_survives hm _ (j2_word0_second_c hm)
    · rw [j2_word0_final_b_start hm]
      exact j2_word0_final_chain hm
  have hcontact := scanl_chain_append_at (survivingGraph m) (c m)
    (contactAnchor (j2Contact hm)) (uWord m (m - 2))
    (c m :: uWord m (m - 1)) hContact (j2_word0_contact_chain hm) hfinal
  have htail : (List.scanl (· * ·) (1 : Configuration m)
      (c m :: (uWord m (m - 2) ++ c m :: uWord m (m - 1)))).IsChain
        (survivingGraph m).Adj := by
    apply scanl_chain_cons
    · simpa only [one_mul] using j2_c_survives hm 1 (j2_word0_first_c hm)
    · simpa only [one_mul] using hcontact
  have h := scanl_chain_append_at (survivingGraph m) (wordStart m 0) 1
    [a m, b m] _ (by simpa only [List.prod_cons, List.prod_nil, mul_one,
      ← mul_assoc] using j2_word0_first_seed hm) (j2_word0_initial_chain hm) htail
  simpa only [word, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.cons_append, List.nil_append,
    List.append_assoc] using h

private theorem j2_word1_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 1) (word m 1)).IsChain
      (survivingGraph m).Adj := by
  let repeatedCH := (List.replicate (m - 3) ([c m] ++ uWord m m)).flatten
  have hlast : a m * repeatedCH.prod * c m = lowerPort (j2Contact hm) := by
    have h := j2_word1_final_a_start hm
    rw [j2_word1_seed hm] at h
    simpa only [repeatedCH, j2_repeated_ch_product] using h
  have htail : (List.scanl (· * ·) (a m * repeatedCH.prod)
      [c m, a m]).IsChain (survivingGraph m).Adj := by
    apply scanl_chain_cons
    · rw [show repeatedCH.prod = (c m * b m) ^ (m - 3) by
        exact j2_repeated_ch_product _ _]
      exact j2_c_survives hm _ (j2_word1_repeated_c hm ⟨m - 3, by omega⟩)
    · rw [hlast]
      exact j2_word1_final_chain hm
  have hmiddle := scanl_chain_append (survivingGraph m) (a m)
    repeatedCH [c m, a m] (j2_word1_repeated_chain hm) htail
  have h := scanl_chain_append_at (survivingGraph m) (wordStart m 1) (a m)
    (List.replicate (m - 1) [a m, b m]).flatten (repeatedCH ++ [c m, a m])
    (by simpa only [List.prod_flatten, List.map_replicate, List.prod_replicate,
      List.prod_cons, List.prod_nil, mul_one] using j2_word1_seed hm)
    (j2_word1_initial_chain hm) hmiddle
  simpa only [word, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, repeatedCH, List.append_assoc] using h

private theorem j2_word2_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 2) (word m 2)).IsChain
      (survivingGraph m).Adj := by
  let repeatedCH := (List.replicate (m - 3) ([c m] ++ uWord m m)).flatten
  let C := contactAnchor (j2Contact hm)
  have hlast : (C * b m) * repeatedCH.prod * c m =
      gapAnchor C ⟨m - 2, by omega⟩ := by
    have h := j2_word2_final_aba_start hm
    rw [j2_word2_seed hm] at h
    simpa only [repeatedCH, C, j2_repeated_ch_product] using h
  have htail : (List.scanl (· * ·) (C * b m * repeatedCH.prod)
      [c m, a m, b m, a m]).IsChain (survivingGraph m).Adj := by
    apply scanl_chain_cons
    · rw [show repeatedCH.prod = (c m * b m) ^ (m - 3) by
        exact j2_repeated_ch_product _ _]
      exact j2_c_survives hm _ (j2_word2_repeated_c hm ⟨m - 3, by omega⟩)
    · rw [hlast]
      exact j2_word2_final_chain hm
  have hmiddle := scanl_chain_append (survivingGraph m) (C * b m)
    repeatedCH [c m, a m, b m, a m] (j2_word2_repeated_chain hm) htail
  have h := scanl_chain_append_at (survivingGraph m) (wordStart m 2) (C * b m)
    [a m] (repeatedCH ++ [c m, a m, b m, a m])
    (by simpa only [List.prod_cons, List.prod_nil, mul_one, C] using j2_word2_seed hm)
    (j2_word2_initial_chain hm) hmiddle
  simpa only [word, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, repeatedCH, List.append_assoc] using h

private theorem j2_word3_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 3) (word m 3)).IsChain
      (survivingGraph m).Adj := by
  have htail : (List.scanl (· * ·) (wordStart m 3 * a m)
      (c m :: uWord m (m - 2))).IsChain (survivingGraph m).Adj := by
    apply scanl_chain_cons
    · rw [j2_word3_seed hm]
      exact j2_c_survives hm _ (j2_word3_c hm)
    · rw [j2_word3_final_b_start hm]
      exact j2_word3_final_chain hm
  have h := scanl_chain_append (survivingGraph m) (wordStart m 3)
    [a m] (c m :: uWord m (m - 2)) (j2_word3_initial_chain hm)
    (by simpa only [List.prod_cons, List.prod_nil, mul_one] using htail)
  simpa only [word, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.cons_append, List.nil_append] using h

private theorem j2_word4_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 4) (word m 4)).IsChain
      (survivingGraph m).Adj := by
  have htail : (List.scanl (· * ·) (wordStart m 4 * (a m * b m))
      (c m :: uWord m (m - 1))).IsChain (survivingGraph m).Adj := by
    apply scanl_chain_cons
    · rw [← mul_assoc, j2_word4_seed hm]
      exact j2_c_survives hm _ (j2_word4_c hm)
    · rw [← mul_assoc, j2_word4_final_b_start hm]
      exact j2_word4_final_chain hm
  have h := scanl_chain_append (survivingGraph m) (wordStart m 4)
    [a m, b m] (c m :: uWord m (m - 1)) (j2_word4_initial_chain hm)
    (by simpa only [List.prod_cons, List.prod_nil, mul_one] using htail)
  simpa only [word, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.cons_append, List.nil_append] using h

private theorem actual_j2_word_chain {m : ℕ} (hm : 5 ≤ m) (i : Fin 5) :
    (List.scanl (· * ·) (wordStart m i) (word m i)).IsChain
      (survivingGraph m).Adj := by
  fin_cases i
  · exact j2_word0_chain hm
  · exact j2_word1_chain hm
  · exact j2_word2_chain hm
  · exact j2_word3_chain hm
  · exact j2_word4_chain hm


private theorem word_foldl {m : ℕ} (z : Configuration m)
    (l : List (Configuration m)) : l.foldl (· * ·) z = z * l.prod := by
  induction l generalizing z with
  | nil => simp
  | cons g gs ih => simp [ih, mul_assoc]

/-- Once actual step legality is earned, no path, simplicity, or component
coverage hypothesis is needed to obtain the complete J2 path component. -/
private theorem actual_j2_word_full_component {m : ℕ} (hm : 5 ≤ m) (i : Fin 5)
    (hchain : (List.scanl (· * ·) (wordStart m i) (word m i)).IsChain
      (survivingGraph m).Adj) :
    ∃ w : (survivingGraph m).Walk (wordStart m i) (wordFinish m i),
      w.IsPath ∧ w.length = wordLength m i ∧
        w.support = List.scanl (· * ·) (wordStart m i) (word m i) ∧
        (∀ x, x ∈ w.support ↔ (survivingGraph m).Reachable (wordStart m i) x) ∧
        ∀ x y, (survivingGraph m).Adj x y ∧
          (survivingGraph m).Reachable (wordStart m i) x ↔ s(x, y) ∈ w.edges := by
  classical
  let xs := List.scanl (· * ·) (wordStart m i) (word m i)
  have hne : xs ≠ [] := List.scanl_ne_nil
  let raw := SimpleGraph.Walk.ofSupport xs hne hchain
  let w := raw.copy (List.head_scanl hne)
    (by rw [List.getLast_scanl, word_foldl, native_j2_word_endpoints hm i])
  have hsupport : w.support = xs := by simp [w, raw]
  have hlength : w.length = wordLength m i := by
    have he := congrArg List.length hsupport
    simp only [SimpleGraph.Walk.length_support, xs, List.length_scanl,
      native_j2_word_lengths hm i] at he
    omega
  have hpositive : 0 < wordLength m i := by
    have hquad : 4 * m + 7 ≤ 2 * m * m := by nlinarith
    fin_cases i <;> simp only [wordLength, Fin.val_mk] <;> omega
  have hnil : ¬w.Nil := by
    intro h
    have he := h.length_eq_zero
    omega
  have hsleaf : ((survivingGraph m).neighborSet (wordStart m i)).Subsingleton := by
    fin_cases i
    · exact actual_port_leaf hm (0, false, false)
    · exact actual_port_leaf hm (0, false, true)
    · exact actual_port_leaf hm (1, false, false)
    · exact actual_port_leaf hm (2, false, true)
    · exact actual_port_leaf hm (0, true, false)
  have hfleaf : ((survivingGraph m).neighborSet (wordFinish m i)).Subsingleton := by
    fin_cases i
    · exact actual_port_leaf hm (2, false, false)
    · exact actual_port_leaf hm (1, true, true)
    · exact actual_port_leaf hm (2, true, true)
    · exact actual_port_leaf hm (2, true, false)
    · exact actual_port_leaf hm (1, true, false)
  have hnb := literal_trace_nonbacktracking w id (word m i)
    (by simpa only [List.map_id_fun, id_eq, xs] using hsupport) (literal_j2_letters hm i)
  obtain ⟨hp, _, _, _, hvertices, hedges⟩ :=
    nonbacktracking_leaf_full_component w (actual_surviving_degree hm)
      hsleaf hfleaf hnil hnb
  exact ⟨w, hp, hlength, hsupport, hvertices, hedges⟩

/-- Every one of the five independently specified native words is an actual
simple path exhausting its entire component of the actual six-cut F2 graph.
Its literal trace, edge count, endpoints and full edge inventory are earned. -/
theorem native_j2_word_full_component {m : ℕ} (hm : 5 ≤ m) (i : Fin 5) :
    ∃ w : (survivingGraph m).Walk (wordStart m i) (wordFinish m i),
      w.IsPath ∧ w.length = wordLength m i ∧
        w.support = List.scanl (· * ·) (wordStart m i) (word m i) ∧
        (∀ x, x ∈ w.support ↔ (survivingGraph m).Reachable (wordStart m i) x) ∧
        ∀ x y, (survivingGraph m).Adj x y ∧
          (survivingGraph m).Reachable (wordStart m i) x ↔ s(x, y) ∈ w.edges :=
  actual_j2_word_full_component hm i (actual_j2_word_chain hm i)

#print axioms native_j2_word_full_component
#print axioms actual_j2_word_chain
#print axioms j2_word0_initial_chain
#print axioms j2_word1_initial_chain
#print axioms j2_word4_initial_chain
#print axioms j2_word1_final_chain
#print axioms j2_word2_initial_chain
#print axioms j2_word2_final_chain
#print axioms j2_word3_initial_chain
#print axioms j2_word4_final_chain

#print axioms j2_word0_contact_chain
#print axioms j2_word0_final_chain
#print axioms j2_word3_final_chain
#print axioms actual_j2_word_full_component
#print axioms j2_word1_repeated_c
#print axioms j2_word2_repeated_c
#print axioms j2_c_survives
#print axioms j2_h_lower_survives
#print axioms j2_h_newgap_survives
#print axioms j2_word1_repeated_chain
#print axioms j2_word2_repeated_chain


end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
