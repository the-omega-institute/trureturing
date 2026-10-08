/- GID: D5/S3/Combinatorics/DihedralRamsey/MonotoneRamseyBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/MonotoneRamseyBlocks
   mirror-E: none(waiver:shared-monotone-block-obstructions)
   anchors: []
   utility: none
   digest: Consecutive block colouring avoids monotone paths and connected red patterns. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyBlocks
import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyCopies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs

theorem block_mono_red_avoiding {a n : ℕ} (ha : 2 ≤ a) :
    ¬DihedralEmbeddable (monoPath a)
      (SimpleGraph.fromRel fun x y : Fin n => x.val / (a - 1) = y.val / (a - 1)) := by
  classical
  rintro ⟨s, refl, ψ, hψ, he⟩
  let f : Fin a → Fin n := fun i => ψ (dihedralPerm s refl i)
  have hf : Function.Injective f := hψ.injective.comp (dihedralPerm_injective a s refl)
  let z : Fin a := ⟨0, by omega⟩
  have same : ∀ (j : ℕ) (hj : j < a),
      (f ⟨j, hj⟩).val / (a - 1) = (f z).val / (a - 1) := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
        intro hj
        have edge := he (⟨j, by omega⟩ : Fin a) ⟨j + 1, hj⟩
          ((SimpleGraph.fromRel_adj _ _ _).mpr
            ⟨by intro h; have hval := congrArg Fin.val h;
                change j = j + 1 at hval; omega, Or.inl rfl⟩)
        have eqv : (f ⟨j, by omega⟩).val / (a - 1) =
            (f ⟨j + 1, hj⟩).val / (a - 1) := by
          rcases edge.2 with h | h
          · exact h
          · exact h.symm
        exact eqv.symm.trans (ih (by omega))
  apply block_path_avoiding ha
  refine ⟨s, refl, ψ, hψ, ?_⟩
  intro i j hij
  apply (SimpleGraph.fromRel_adj _ _ _).mpr
  exact ⟨hf.ne ((altPath a).ne_of_adj hij),
    Or.inl ((same i.val i.isLt).trans (same j.val j.isLt).symm)⟩

theorem block_star_red_avoiding {a n : ℕ} (ha : 2 ≤ a) :
    ¬DihedralEmbeddable (startStar a)
      (SimpleGraph.fromRel fun x y : Fin n => x.val / (a - 1) = y.val / (a - 1)) := by
  classical
  rintro ⟨s, refl, ψ, hψ, he⟩
  let f : Fin a → Fin n := fun i => ψ (dihedralPerm s refl i)
  have hf : Function.Injective f := hψ.injective.comp (dihedralPerm_injective a s refl)
  let z : Fin a := ⟨0, by omega⟩
  have same : ∀ i : Fin a, (f i).val / (a - 1) = (f z).val / (a - 1) := by
    intro i
    by_cases hi : i = z
    · rw [hi]
    have edge := he z i ((SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨Ne.symm hi, Or.inl ⟨rfl, by intro hz; exact hi (Fin.ext hz)⟩⟩)
    have eqv : (f z).val / (a - 1) = (f i).val / (a - 1) := by
      rcases edge.2 with h | h
      · exact h
      · exact h.symm
    exact eqv.symm
  apply block_path_avoiding ha
  refine ⟨s, refl, ψ, hψ, ?_⟩
  intro i j hij
  apply (SimpleGraph.fromRel_adj _ _ _).mpr
  exact ⟨hf.ne ((altPath a).ne_of_adj hij), Or.inl ((same i).trans (same j).symm)⟩

theorem block_mono_blue_avoiding {b n d : ℕ} (hb : 3 ≤ b) (hd : 0 < d)
    (hn : n ≤ d * (b - 2)) :
    ¬DihedralEmbeddable (monoPath b)
      (SimpleGraph.fromRel fun x y : Fin n => x.val / d = y.val / d)ᶜ := by
  classical
  let : NeZero b := ⟨by omega⟩
  intro he
  obtain ⟨ψ, hψ, t, hedge⟩ :=
    (monotone_cyclic_iff_gaps (by omega) _).mp
      ((monotone_dihedral_iff_cyclic (by omega) _).mp he)
  have step : ∀ (j : ℕ) (hj : j + 1 < b),
      (ψ ⟨j, by omega⟩).val / d ≤ (ψ ⟨j + 1, hj⟩).val / d ∧
      (j ≠ t.val → (ψ ⟨j, by omega⟩).val / d < (ψ ⟨j + 1, hj⟩).val / d) := by
    intro j hj
    let i : Fin b := ⟨j, by omega⟩
    let k : Fin b := ⟨j + 1, hj⟩
    have mono : (ψ i).val / d ≤ (ψ k).val / d :=
      Nat.div_le_div_right (hψ.monotone (by change j ≤ j + 1; omega))
    refine ⟨mono, ?_⟩
    intro hne
    have hit : i ≠ t := by intro h; exact hne (congrArg Fin.val h)
    have hik : i + 1 = k := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt' (by simpa [i] using hj)
    have he := hedge i hit
    rw [hik] at he
    exact block_blue_quotient_lt
      (hψ (show i < k by change j < j + 1; omega)) he
  have bound : ∀ (j : ℕ) (hj : j < b),
      j ≤ (ψ ⟨j, hj⟩).val / d + (if t.val < j then 1 else 0) := by
    intro j
    induction j with
    | zero => intro hj; exact Nat.zero_le _
    | succ j ih =>
        intro hj
        have h := step j hj
        have h' := ih (by omega)
        by_cases heq : j = t.val
        · split_ifs at h' ⊢ <;> omega
        · have hs := h.2 heq
          split_ifs at h' ⊢ <;> omega
  let last : Fin b := ⟨b - 1, by omega⟩
  have small : (ψ last).val / d < b - 2 := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have h := lt_of_lt_of_le (ψ last).isLt hn
    simpa only [Nat.mul_comm] using h
  have large := bound (b - 1) (by omega)
  change b - 1 ≤ (ψ last).val / d + (if t.val < b - 1 then 1 else 0) at large
  split_ifs at large <;> omega

end D5.S3.Combinatorics.DihedralRamsey
