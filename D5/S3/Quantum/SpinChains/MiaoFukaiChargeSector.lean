/- GID: D5/S3/Quantum/SpinChains/MiaoFukaiChargeSector
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/MiaoFukaiChargeSector
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Explicit labelled jammed configurations at one odd-deficit charge. -/

module

public import D5.S3.Quantum.SpinChains.MiaoFukaiGuardedMoves
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Chain
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.IntervalCases

/-! The explicit A/B tile witness in issue #35234. Splitting a two-empty gap
into its first and second vacancies permits a single adjacency rule at all joins. -/

public section

open scoped BigOperators Matrix

namespace D5.S3.Quantum.SpinChains.MiaoFukaiGuardedMoves

def blocks (L : ℕ) : ℕ := (L - 8) / 5

private def residue (L : ℕ) : ℕ := (L - 8) % 5

private def tailZeros (t : ℕ) : ℕ := if t = 2 then 2 else if t = 0 ∨ t = 3 then 1 else 0

private def padWithSingles (L : ℕ) : Bool :=
  decide ((blocks L + tailZeros (residue L)) % 2 = 0)

private def deficit (L : ℕ) : ℕ :=
  blocks L + tailZeros (residue L) + if padWithSingles L then 3 else 0

def targetCharge (L : ℕ) : ℕ := L - deficit L

private inductive Cell where
  | occupied
  | single
  | first
  | second
  deriving DecidableEq

private def Cell.rung : Cell → Rung
  | .occupied => .minus
  | _ => .e

private def Cell.mark (c : Cell) : ℕ := if c = .single then 1 else 0

private def Edge : Cell → Cell → Prop
  | .occupied, .single | .occupied, .first | .first, .second
  | .single, .occupied | .second, .occupied => True
  | _, _ => False

private theorem local_window {l c r : Cell} (hl : Edge l c) (hr : Edge c r) :
    (c.rung = .e ∨ r.rung = .e) ∧
    pTriple l.rung c.rung r.rung + c.mark = 1 ∧
    (c.mark = 1 → l.mark = 0 ∧ r.mark = 0) := by
  cases l <;> cases c <;> cases r <;> simp_all [Edge, Cell.rung, Cell.mark, pTriple, bit]

private def tileA : List Cell := [.occupied, .single]

private def tileB : List Cell := [.occupied, .first, .second]

private def block (b : Bool) : List Cell := if b then tileB ++ tileA else tileA ++ tileB

private def tail : ℕ → List Cell
  | 0 => tileA
  | 1 => tileB
  | 2 => tileA ++ tileA
  | 3 => tileA ++ tileB
  | 4 => tileB ++ tileB
  | _ => []

private def pad (b : Bool) : List Cell :=
  if b then tileA ++ tileA ++ tileA else tileB ++ tileB

private def blockCells : {m : ℕ} → (Fin m → Bool) → List Cell
  | 0, _ => []
  | _ + 1, b => block (b 0) ++ blockCells (fun i => b i.succ)

private theorem block_length (b : Bool) : (block b).length = 5 := by cases b <;> rfl

private theorem prefix_length {m : ℕ} (b : Fin m → Bool) :
    (blockCells b).length = 5 * m := by
  induction m with
  | zero => rfl
  | succ n ih =>
    simp only [blockCells, List.length_append, block_length, ih]
    omega

private theorem block_join (b : Bool) (xs : List Cell)
    (hh : xs.head? = some .occupied) (hc : xs.IsChain Edge) :
    (block b ++ xs).head? = some .occupied ∧ (block b ++ xs).IsChain Edge := by
  cases b <;>
    simp [block, tileA, tileB, List.isChain_cons, hh, hc, Edge]

private theorem prefix_join {m : ℕ} (b : Fin m → Bool) (xs : List Cell)
    (hh : xs.head? = some .occupied) (hc : xs.IsChain Edge) :
    (blockCells b ++ xs).head? = some .occupied ∧ (blockCells b ++ xs).IsChain Edge := by
  induction m with
  | zero => exact ⟨hh, hc⟩
  | succ n ih =>
    rw [blockCells, List.append_assoc]
    exact block_join _ _ (ih _).1 (ih _).2

private def cells {L : ℕ} (b : Fin (blocks L) → Bool) : List Cell :=
  blockCells b ++ (tail (residue L) ++ pad (padWithSingles L))

private theorem cells_length {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool) :
    (cells b).length = L := by
  have ht : residue L < 5 := Nat.mod_lt _ (by decide)
  have hl (t : ℕ) (h : t < 5) : (tail t).length = t + 2 := by
    interval_cases t <;> rfl
  have hp (d : Bool) : (pad d).length = 6 := by cases d <;> rfl
  simp only [cells, List.length_append, prefix_length, hl _ ht, hp]
  have hd := Nat.mod_add_div (L - 8) 5
  unfold residue blocks
  omega

private theorem cells_chain {L : ℕ} (b : Fin (blocks L) → Bool) :
    (cells b).head? = some Cell.occupied ∧ (cells b ++ [Cell.occupied]).IsChain Edge := by
  have ht : residue L < 5 := Nat.mod_lt _ (by decide)
  have hchain (t : ℕ) (h : t < 5) (d : Bool) :
      (tail t ++ pad d).head? = some Cell.occupied ∧
        ((tail t ++ pad d) ++ [Cell.occupied]).IsChain Edge := by
    interval_cases t <;> cases d <;>
      simp [tail, pad, tileA, tileB, List.isChain_cons, Edge]
  have h := hchain _ ht (padWithSingles L)
  have hend : ((tail (residue L) ++ pad (padWithSingles L)) ++ [Cell.occupied]).head? =
      some Cell.occupied := by rw [List.head?_append, h.1, Option.some_or]
  have hj := prefix_join b _ hend h.2
  refine ⟨?_, by simpa only [cells, List.append_assoc] using hj.2⟩
  rw [cells, List.head?_append, h.1]
  have hhead := hj.1
  rw [List.head?_append, hend] at hhead
  exact hhead

private theorem cells_marks {L : ℕ} (b : Fin (blocks L) → Bool) :
    ((cells b).map Cell.mark).sum = deficit L := by
  have hb (d : Bool) : ((block d).map Cell.mark).sum = 1 := by cases d <;> rfl
  have hprefix {m : ℕ} (f : Fin m → Bool) : ((blockCells f).map Cell.mark).sum = m := by
    induction m with
    | zero => rfl
    | succ n ih =>
      simp only [blockCells, List.map_append, List.sum_append, hb, ih]
      omega
  have ht (t : ℕ) (h : t < 5) : ((tail t).map Cell.mark).sum = tailZeros t := by
    interval_cases t <;> rfl
  have hp (d : Bool) : ((pad d).map Cell.mark).sum = if d then 3 else 0 := by
    cases d <;> rfl
  have htail := ht (residue L) (Nat.mod_lt _ (by decide))
  simp only [cells, deficit, List.map_append, List.sum_append, hprefix, htail, hp, Nat.add_assoc]

private theorem prefix_decode {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    ((blockCells b).getD (5 * i.val + 2) .occupied).rung =
      if b i then Rung.e else .minus := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [blockCells, List.getD_append _ _ _ _ (by simp [block_length])]
      cases h : b 0 <;> simp [block, tileA, tileB, Cell.rung, List.getD]
    · rw [blockCells, List.getD_append_right _ _ _ _ (by
        rw [block_length]
        have h := j.isLt
        simp only [Fin.val_succ]
        omega)]
      have he : 5 * j.succ.val + 2 - (block (b 0)).length = 5 * j.val + 2 := by
        rw [block_length]
        simp only [Fin.val_succ]
        omega
      rw [he]
      exact ih (fun k => b k.succ) j

private def cellAt {L : ℕ} (b : Fin (blocks L) → Bool) (j : Fin L) : Cell :=
  (cells b).getD j.val .occupied

private theorem cells_edge {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool)
    (j : Fin L) : Edge (cellAt b j) (cellAt b (next j)) := by
  obtain ⟨hfirst, hchain⟩ := cells_chain b
  have hlen := cells_length hL b
  have hj := j.isLt
  have hstep := List.isChain_iff_getElem.mp hchain j.val (by simp [hlen])
  have hget (k : ℕ) (hk : k < L) :
      (cells b ++ [.occupied])[k]'(by simp [hlen]; omega) =
        (cells b).getD k .occupied := by
    rw [List.getElem_append_left (by simpa only [hlen] using hk),
      List.getD_eq_getElem _ _ (by simpa only [hlen] using hk)]
  rw [hget j.val hj] at hstep
  unfold cellAt
  rw [next_val]
  split
  · rw [hget _ (by assumption)] at hstep
    exact hstep
  · have hend : j.val + 1 = L := by omega
    have hzero : (cells b).getD 0 .occupied = .occupied := by
      rw [List.head?_eq_getElem?] at hfirst
      rw [List.getD_eq_getElem?_getD, hfirst, Option.getD_some]
    rw [hzero]
    have hlast : ((cells b ++ [.occupied])[j.val + 1]'(by simp [hlen])) =
        Cell.occupied := by
      rw [List.getElem_append_right (by rw [hlen, hend])]
      simp [hlen, hend]
    rw [hlast] at hstep
    exact hstep

private theorem cell_window {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool)
    (j : Fin L) :
    ((cellAt b j).rung = .e ∨ (cellAt b (next j)).rung = .e) ∧
      pTriple (cellAt b (prev j)).rung (cellAt b j).rung (cellAt b (next j)).rung +
        (cellAt b j).mark = 1 ∧
      ((cellAt b j).mark = 1 →
        (cellAt b (prev j)).mark = 0 ∧ (cellAt b (next j)).mark = 0) := by
  have hl := cells_edge hL b (prev j)
  rw [show next (prev j) = j from (finRotate L).apply_symm_apply j] at hl
  exact local_window hl (cells_edge hL b j)

/-- The labelled periodic word formed from the prescribed blocks, tail and pad. -/
def tiledConfig {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool) : Config L :=
  ⟨fun j => (cellAt b j).rung, fun j => (cell_window hL b j).1⟩

private theorem tiled_mark {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool) (j : Fin L) :
    p (tiledConfig hL b) j + (cellAt b j).mark = 1 :=
  (cell_window hL b j).2.1

private theorem tiled_jammed {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool) :
    Jammed (tiledConfig hL b) := by
  intro j hp
  have hm := tiled_mark hL b j
  have hs : (cellAt b j).mark = 1 := by omega
  obtain ⟨hl, hr⟩ := (cell_window hL b j).2.2 hs
  have hleft := tiled_mark hL b (prev j)
  have hright := tiled_mark hL b (next j)
  exact ⟨by omega, by omega⟩

private theorem sum_marks {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool) :
    (∑ j : Fin L, (cellAt b j).mark) = deficit L := by
  have hlen := cells_length hL b
  have htransport := (finCongr hlen).sum_comp (fun j : Fin L => (cellAt b j).mark)
  rw [← htransport, ← Fin.sum_ofFn]
  have he : List.ofFn (fun j : Fin (cells b).length =>
      (cellAt b (finCongr hlen j)).mark) = (cells b).map Cell.mark := by
    rw [← List.ofFn_getElem_eq_map]
    congr 1
    funext j
    unfold cellAt
    rw [show (finCongr hlen j).val = j.val from rfl, List.getD_eq_getElem _ _ j.isLt]
  rw [he]
  exact cells_marks b

private theorem tiled_charge_add {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool) :
    charge (tiledConfig hL b) + deficit L = L := by
  rw [← sum_marks hL b, charge, ← Finset.sum_add_distrib]
  simp [tiled_mark]

private theorem tiled_injective {L : ℕ} (hL : 12 ≤ L) :
    Function.Injective (tiledConfig hL) := by
  intro b c h
  funext i
  have index_lt : 5 * i.val + 2 < 5 * blocks L := by
    have hi := i.isLt
    omega
  have hp : 5 * blocks L ≤ L := by
    have hl := cells_length hL b
    simp only [cells, List.length_append, prefix_length] at hl
    omega
  let j : Fin L := ⟨5 * i.val + 2, by omega⟩
  have hd (f : Fin (blocks L) → Bool) :
      (tiledConfig hL f).val j = if f i then Rung.e else .minus := by
    change ((cells f).getD (5 * i.val + 2) .occupied).rung = _
    rw [cells, List.getD_append _ _ _ _ (by rw [prefix_length]; exact index_lt)]
    exact prefix_decode f i
  have he := congrArg (fun x : Config L => x.val j) h
  rw [hd, hd] at he
  cases hb : b i <;> cases hc : c i <;> simp_all

abbrev JamSector (L q : ℕ) := {x : Config L // charge x = q ∧ Jammed x}

noncomputable instance jamSectorFintype (L q : ℕ) : Fintype (JamSector L q) := by
  classical
  unfold JamSector
  infer_instance

def jamEmbedding {L : ℕ} (hL : 12 ≤ L) :
    (Fin (blocks L) → Bool) ↪ JamSector L (targetCharge L) where
  toFun b := ⟨tiledConfig hL b, by
    have h := tiled_charge_add hL b
    unfold targetCharge
    omega, tiled_jammed hL b⟩
  inj' := fun _ _ h => tiled_injective hL (congrArg Subtype.val h)

/-- Forgetting the sector proof recovers the labelled tile word. -/
theorem jamEmbedding_val {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool) :
    (jamEmbedding hL b).val = tiledConfig hL b := (rfl)

/-- The witness image has exactly the stated size and lies in a sector with odd deficit. -/
theorem jammed_charge_count {L : ℕ} (hL : 12 ≤ L) :
    Odd (L - targetCharge L) ∧
      (Finset.univ.map (jamEmbedding hL)).card = 2 ^ blocks L ∧
      2 ^ blocks L ≤ Fintype.card (JamSector L (targetCharge L)) := by
  constructor
  · have hbound := tiled_charge_add hL (fun _ => false)
    have hdef : L - targetCharge L = deficit L := by unfold targetCharge; omega
    rw [hdef, Nat.odd_iff]
    by_cases h : (blocks L + tailZeros (residue L)) % 2 = 0
    · simp [deficit, padWithSingles, h]
      omega
    · simp [deficit, padWithSingles, h]
      omega
  constructor
  · simp
  · simpa only [Fintype.card_pi_const, Fintype.card_bool, Fintype.card_fin] using
      Fintype.card_le_of_injective (jamEmbedding hL) (jamEmbedding hL).injective

/-- Every prescribed word has the common projector charge and zero local row and column. -/
theorem witness_local_actions {L : ℕ} (hL : 12 ≤ L) (b : Fin (blocks L) → Bool) :
    NP L *ᵥ ket (tiledConfig hL b) = (targetCharge L : ℂ) • ket (tiledConfig hL b) ∧
    ∀ j : Fin L, T j *ᵥ ket (tiledConfig hL b) = 0 ∧
      ket (tiledConfig hL b) ᵥ* T j = 0 := by
  have hc : charge (tiledConfig hL b) = targetCharge L := (jamEmbedding hL b).property.1
  refine ⟨?_, fun j => jammed_kills (by omega) j (tiled_jammed hL b)⟩
  rw [charge_eigenvalue, hc]

end D5.S3.Quantum.SpinChains.MiaoFukaiGuardedMoves
