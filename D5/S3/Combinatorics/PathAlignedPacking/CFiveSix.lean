/- GID: D5/S3/Combinatorics/PathAlignedPacking/CFiveSix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/CFiveSix
   mirror-E: none(waiver:direct-settlement-of-exceptional-family)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Walk.Maps]
   utility: none
   digest: Chains of at least five C5 blocks have packing chromatic number six. -/

import D5.S3.Combinatorics.PathAlignedPacking.CFiveDP
import D5.S3.Combinatorics.PathAlignedPacking.SixTemplate
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.CFiveSix

open Defs
open D5.S3.Combinatorics.PathAlignedPacking.Metric CFiveData CFiveDP

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def inclusion (t : ℕ) (ht : 5 ≤ t) : graph 5 5 5 →g graph 5 5 t := {
  toFun v := (⟨v.1.val, by have := v.1.isLt; omega⟩, v.2)
  map_rel' := by
    intro u v h
    refine ⟨?_, h.2⟩
    intro heq
    apply h.1
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z : Vertex t 5 => z.1.val) heq
    · exact congrArg (fun z : Vertex t 5 => z.2) heq

}

private def block (f : Vertex 5 5 → ℕ) (hf : PackingColoring (graph 5 5 5) 5 f)
    (i : Fin 5) : Block := fun j =>
  ⟨f (i, j) - 1, by have := hf.1 (i, j); omega⟩

/-- The exceptional family has exactly the claimed lower and upper packing bounds. -/
theorem result : claimCFiveSix := by

  have restrict (t : ℕ) (ht : 5 ≤ t) :
      HasPacking (graph 5 5 t) 5 → HasPacking (graph 5 5 5) 5 := by
    have inclusion_injective (t : ℕ) (ht : 5 ≤ t) :
        Function.Injective (inclusion t ht) := by
      intro u v h
      apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun z : Vertex t 5 => z.1.val) h
      · exact congrArg (fun z : Vertex t 5 => z.2) h

    rintro ⟨f, hf⟩
    refine ⟨fun v => f (inclusion t ht v), ?_, ?_⟩
    · intro v; exact hf.1 _
    · intro u v hne heq p
      have hne' : inclusion t ht u ≠ inclusion t ht v :=
        fun h => hne (inclusion_injective t ht h)
      have hdist := hf.2 _ _ hne' heq (p.map (inclusion t ht))
      simpa only [SimpleGraph.Walk.length_map] using hdist

  intro t ht
  constructor
  · intro h
    have no_five : ¬ HasPacking (graph 5 5 5) 5 := by
      clear h ht t
      have necessary (f : Vertex 5 5 → ℕ) (hf : PackingColoring (graph 5 5 5) 5 f)
          (u v : Vertex 5 5) (hne : u ≠ v) (heq : f u = f v) :
          (f u : ℤ) < chainSep 4 1 (point u) (point v) := by
        have checked : ∀ x y : Vertex 5 5,
            ((x :: route x y).IsChain (graph 5 5 5).Adj) ∧
              (x :: route x y).getLast (by simp) = y ∧
              ((route x y).length : ℤ) = chainSep 4 1 (point x) (point y) := by
          decide +kernel
        obtain ⟨hr, hend, hlen⟩ := checked u v
        have hw : ∃ p : (graph 5 5 5).Walk u ((u :: route u v).getLast (by simp)),
            p.length = (route u v).length := by
          refine ⟨SimpleGraph.Walk.ofSupport (u :: route u v) (by simp) hr, ?_⟩
          simpa using SimpleGraph.Walk.length_ofSupport (l := u :: route u v) (by simp) hr
        rw [hend] at hw
        obtain ⟨p, hp⟩ := hw
        have hlt := hf.2 u v hne heq p
        omega

      have block_value (f : Vertex 5 5 → ℕ) (hf : PackingColoring (graph 5 5 5) 5 f)
          (i j : Fin 5) : (block f hf i j).val + 1 = f (i, j) := by
        have := hf.1 (i, j)
        dsimp [block]
        omega

      have block_equal (f : Vertex 5 5 → ℕ) (hf : PackingColoring (graph 5 5 5) 5 f)
          (i j x y : Fin 5) (heq : block f hf i x = block f hf j y) : f (i, x) = f (j, y) := by
        have hval := congrArg Fin.val heq
        have hu := block_value f hf i x
        have hv := block_value f hf j y
        omega

      have pair (f : Vertex 5 5 → ℕ) (hf : PackingColoring (graph 5 5 5) 5 f)
          (i j : Fin 5) (d : ℕ) (hd : 0 < d) (hij : i.val + d = j.val) :
          PairOK d (block f hf i) (block f hf j) := by
        have check (x y : Fin 5) (heq : block f hf i x = block f hf j y) :
            ((block f hf i x).val + 1 : ℤ) < 2 * (d : ℤ) - 1 +
              ((![1, 2, 2, 1, 0] : Fin 5 → ℤ) x +
                (![0, 1, 2, 2, 1] : Fin 5 → ℤ) y) := by
          have hne : (i, x) ≠ (j, y) := by
            intro h
            have hh : i.val = j.val := congrArg (fun z : Vertex 5 5 => z.1.val) h
            omega
          have hs := necessary f hf (i, x) (j, y) hne (block_equal f hf i j x y heq)
          rw [← block_value f hf i x] at hs
          have hijlt : i.val < j.val := by omega
          have hcast : (j.val : ℤ) - (i.val : ℤ) = d := by omega
          fin_cases x <;> fin_cases y <;>
            simp [chainSep, point, cycleSep, hijlt, ne_of_lt hijlt, hcast] at hs ⊢ <;> omega
        unfold PairOK
        repeat' constructor
        · intro heq
          have hh := check 4 0 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 0 0 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 3 0 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 4 1 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 4 4 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 1 0 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 2 0 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 4 2 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 4 3 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 0 1 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 0 4 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 3 1 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 3 4 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 0 2 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 0 3 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 1 1 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 1 4 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 2 1 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 2 4 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 3 2 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 3 3 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 1 2 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 1 3 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 2 2 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega
        · intro heq
          have hh := check 2 3 heq
          dsimp only [Matrix.cons_val] at hh
          norm_num at hh ⊢
          omega

      have decode_encode (f : Block) : decode (encode f) = f := by
        funext j
        apply Fin.ext
        have h0 := (f 0).isLt
        have h1 := (f 1).isLt
        have h2 := (f 2).isLt
        have h3 := (f 3).isLt
        have h4 := (f 4).isLt
        fin_cases j <;> dsimp only [decode, encode] <;> norm_num
        · change _ = (f 0).val
          omega
        · change _ = (f 1).val
          omega
        · change _ = (f 2).val
          omega
        · change _ = (f 3).val
          omega
        · change _ = (f 4).val
          omega

      have single (f : Vertex 5 5 → ℕ) (hf : PackingColoring (graph 5 5 5) 5 f)
          (i : Fin 5) : ∀ x y : Fin 5, x ≠ y → block f hf i x = block f hf i y →
          ((block f hf i x).val + 1 : ℤ) < cycleSep 5 x.val y.val := by
        intro x y hne heq
        have hvne : (i, x) ≠ (i, y) := by intro h; exact hne (congrArg Prod.snd h)
        have hs := necessary f hf (i, x) (i, y) hvne (block_equal f hf i i x y heq)
        rw [← block_value f hf i x] at hs
        simpa [chainSep, point] using hs

      have no_chain (f : Fin 5 → Block)
          (hs : ∀ i x y : Fin 5, x ≠ y → f i x = f i y →
            ((f i x).val + 1 : ℤ) < cycleSep 5 x.val y.val)
          (hp : ∀ i j : Fin 5, ∀ d : ℕ, 0 < d → i.val + d = j.val →
            PairOK d (f i) (f j)) : False := by
        have codes_size : codes.size = 240 := by decide +kernel
        have complete_codes : ∀ q : Fin 3125,
            (∀ x y : Fin 5, x ≠ y → decode q x = decode q y →
              ((decode q x).val + 1 : ℤ) < cycleSep 5 x.val y.val) → q.val ∈ codes := by
          decide +kernel
        have hc (i : Fin 5) : ∃ k : Fin 240, candidate k = f i := by
          let r := encode (f i)
          have hdecode : decode r = f i := decode_encode (f i)
          have hvalid : ∀ x y : Fin 5, x ≠ y → decode r x = decode r y →
              ((decode r x).val + 1 : ℤ) < cycleSep 5 x.val y.val := by
            rw [hdecode]; exact hs i
          obtain ⟨j, hj, hget⟩ := Array.mem_iff_getElem.mp (complete_codes r hvalid)
          let k : Fin 240 := ⟨j, by rw [codes_size] at hj; exact hj⟩
          have hgetD : codes.getD j 0 = r.val := by
            rw [← Array.getElem_eq_getD (h := hj) 0, hget]
          refine ⟨k, ?_⟩
          rw [← hdecode]
          apply congrArg decode
          apply Fin.ext
          change codes.getD j 0 % 3125 = r.val
          rw [hgetD, Nat.mod_eq_of_lt r.isLt]
        choose index hindex using hc
        have one (i j : Fin 5) (hij : i.val + 1 = j.val) :
            PairOK 1 (candidate (index i)) (candidate (index j)) := by
          rw [hindex i, hindex j]
          exact hp i j 1 (by omega) hij
        have two (i j : Fin 5) (hij : i.val + 2 = j.val) :
            PairOK 2 (candidate (index i)) (candidate (index j)) := by
          rw [hindex i, hindex j]
          exact hp i j 2 (by omega) hij
        let fidx (i : ℕ) : Fin 240 := index ⟨i % 5, Nat.mod_lt _ (by omega)⟩
        have h5 := propagate fidx 3 (by
          intro i hi
          apply one ⟨i % 5, Nat.mod_lt _ (by omega)⟩
            ⟨(i + 1) % 5, Nat.mod_lt _ (by omega)⟩
          simp only [Fin.val_mk]
          omega) (by
          intro i hi
          apply two ⟨i % 5, Nat.mod_lt _ (by omega)⟩
            ⟨(i + 2) % 5, Nat.mod_lt _ (by omega)⟩
          simp only [Fin.val_mk]
          omega)
        have hthree : extend layerTwo = layerThree := by decide +kernel
        have hfour : extend layerThree = layerFour := by decide +kernel
        have hempty : extend layerFour = [] := by decide +kernel
        simpa only [reachable, hthree, hfour, hempty, List.not_mem_nil] using h5
      rintro ⟨f, hf⟩
      exact no_chain (block f hf) (single f hf) (pair f hf)
    exact no_five (restrict t ht h)
  · apply metric_to_packing 5 5 t 6 (by omega) (by omega)
    simpa using SixTemplate.colouring 0 0 (by omega) (by omega) rfl rfl

end D5.S3.Combinatorics.PathAlignedPacking.CFiveSix
