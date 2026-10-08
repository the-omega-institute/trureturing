/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyBlocks
   mirror-E: none(waiver:shared-ramsey-bounds)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Block obstructions and colouring fibres give shared sharp Ramsey bounds. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyRanks
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPermutations
import D5.S3.Combinatorics.DihedralRamsey.CyclicRamseyDefs
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyColoring
import Mathlib.Data.Finset.Sort
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyFibres

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs CyclicRamseyDefs

theorem block_path_avoiding {a n : ℕ} (ha : 2 ≤ a) :
    ¬DihedralEmbeddable (altPath a)
      (SimpleGraph.fromRel fun x y : Fin n => x.val / (a - 1) = y.val / (a - 1)) := by
  classical
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y =>
    x.val / (a - 1) = y.val / (a - 1)
  have adj : ∀ x y, G.Adj x y ↔ x ≠ y ∧ x.val / (a - 1) = y.val / (a - 1) := by
    intro x y
    simp [G, SimpleGraph.fromRel_adj, eq_comm]
  rintro ⟨s, refl, ψ, hψ, hpath⟩
  obtain ⟨q, hq, _⟩ := alternating_ranks a
  let f : Fin a → Fin n := fun j => ψ (dihedralPerm s refl (q j))
  have hf : Function.Injective f :=
    hψ.injective.comp ((dihedralPerm_injective a s refl).comp q.injective)
  have consecutive : ∀ (j : ℕ) (hj : j + 1 < a),
      (f ⟨j, by omega⟩).val / (a - 1) = (f ⟨j + 1, hj⟩).val / (a - 1) := by
    intro j hj
    apply (adj _ _).mp (hpath _ _ ?_) |>.2
    apply SimpleGraph.fromRel_adj _ _ _ |>.mpr
    refine ⟨?_, Or.inl ⟨j, hj, hq _, hq _⟩⟩
    exact fun h => by
      have heq := congrArg Fin.val (q.injective h)
      change j = j + 1 at heq
      omega
  let z : Fin a := ⟨0, by omega⟩
  have same : ∀ (j : ℕ) (hj : j < a),
      (f ⟨j, hj⟩).val / (a - 1) = (f z).val / (a - 1) := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
        intro hj
        exact (consecutive j hj).symm.trans (ih (by omega))
  let r : Fin a → Fin (a - 1) := fun j =>
    ⟨(f j).val % (a - 1), Nat.mod_lt _ (by omega)⟩
  have hr : Function.Injective r := by
    intro i j hij
    apply hf
    apply Fin.ext
    have hm : (f i).val % (a - 1) = (f j).val % (a - 1) :=
      congrArg Fin.val hij
    have hs := (same i.val i.isLt).trans (same j.val j.isLt).symm
    calc
      (f i).val = (f i).val % (a - 1) + (a - 1) * ((f i).val / (a - 1)) :=
        (Nat.mod_add_div _ _).symm
      _ = (f j).val % (a - 1) + (a - 1) * ((f j).val / (a - 1)) := by rw [hm, hs]
      _ = (f j).val := Nat.mod_add_div _ _
  have := Fintype.card_le_of_injective r hr
  simp only [Fintype.card_fin] at this
  omega

/-- An increasing blue edge crosses to a strictly larger quotient block. -/
theorem block_blue_quotient_lt {n d : ℕ} {x y : Fin n} (hxy : x < y)
    (hedge : (SimpleGraph.fromRel fun u v : Fin n => u.val / d = v.val / d)ᶜ.Adj x y) :
    x.val / d < y.val / d := by
  apply lt_of_le_of_ne (Nat.div_le_div_right (Fin.le_def.mp hxy.le))
  intro heq
  exact (SimpleGraph.compl_adj _ _ _).mp hedge |>.2
    ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hxy.ne, Or.inl heq⟩)

theorem block_clique_avoiding {a b n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hn : n ≤ (a - 1) * (b - 1)) :
    ¬DihedralEmbeddable (⊤ : SimpleGraph (Fin b))
      (SimpleGraph.fromRel fun x y : Fin n => x.val / (a - 1) = y.val / (a - 1))ᶜ := by
  classical
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y =>
    x.val / (a - 1) = y.val / (a - 1)
  have adj : ∀ x y, G.Adj x y ↔ x ≠ y ∧ x.val / (a - 1) = y.val / (a - 1) := by
    intro x y
    simp [G, SimpleGraph.fromRel_adj, eq_comm]
  rintro ⟨s, refl, ψ, hψ, hclique⟩
  let f : Fin b → Fin n := fun j => ψ (dihedralPerm s refl j)
  have hf : Function.Injective f := hψ.injective.comp (dihedralPerm_injective b s refl)
  let c : Fin b → Fin (b - 1) := fun j =>
    ⟨(f j).val / (a - 1), by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      have h := (f j).isLt
      simpa [Nat.mul_comm] using lt_of_lt_of_le h hn⟩
  have hc : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hb := hclique i j ((SimpleGraph.top_adj _ _).mpr hne)
    have hc := (SimpleGraph.compl_adj _ _ _).mp hb
    apply hc.2
    apply (adj _ _).mpr
    exact ⟨hf.ne hne, congrArg Fin.val hij⟩
  have := Fintype.card_le_of_injective c hc
  simp only [Fintype.card_fin] at this
  omega

open Classical in
theorem clique_of_sparse_induces {a b : ℕ} (ha2 : 2 ≤ a)
    (G : SimpleGraph (Fin (1 + (a - 1) * (b - 1))))
    (sparse : ∀ (m : ℕ) (e : Fin m ↪o Fin (1 + (a - 1) * (b - 1))),
      2 * (G.comap e).edgeFinset.card ≤ (a - 2) * m) :
    CyclicEmbeddable (⊤ : SimpleGraph (Fin b)) Gᶜ := by
  classical
  obtain ⟨C⟩ := colorable_of_sparse_induces G sparse
  have colors : a - 2 + 1 = a - 1 := by omega
  have large : ∃ c : Fin (a - 2 + 1),
      b ≤ (Finset.univ.filter fun v => C v = c).card := by
    obtain ⟨c, _, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (f := C) (n := b - 1)
      (fun _ _ => Finset.mem_univ _) (by simp [colors])
    exact ⟨c, by omega⟩
  obtain ⟨c, hc⟩ := large
  let S := Finset.univ.filter fun v => C v = c
  let e : Fin b ↪o Fin (1 + (a - 1) * (b - 1)) := S.orderEmbOfCardLe hc
  refine ⟨0, e, e.strictMono, ?_⟩
  intro i j hij
  have di : dihedralPerm 0 false i = i := by
    apply Fin.ext
    simp [dihedralPerm, Nat.mod_eq_of_lt i.isLt]
  have dj : dihedralPerm 0 false j = j := by
    apply Fin.ext
    simp [dihedralPerm, Nat.mod_eq_of_lt j.isLt]
  rw [di, dj]
  apply (SimpleGraph.compl_adj _ _ _).mpr
  refine ⟨e.injective.ne ((SimpleGraph.top_adj _ _).mp hij), ?_⟩
  intro hred
  have hi := Finset.mem_filter.mp (S.orderEmbOfCardLe_mem hc i)
  have hj := Finset.mem_filter.mp (S.orderEmbOfCardLe_mem hc j)
  exact C.valid hred (hi.2.trans hj.2.symm)

end D5.S3.Combinatorics.DihedralRamsey
