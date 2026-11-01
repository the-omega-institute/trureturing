/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Physical
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Physical
   mirror-E: none(waiver:private-consumed-occurrence-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: UXWV physical occurrence inventory and both weighted bank masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Supports
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open SourceWidth
open MaxPlusTwo.Chambers
open private Parameters Parameters.a Parameters.b Parameters.c Parameters.d
  Parameters.hc Parameters.hd Parameters.ha Parameters.hb from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
open private lengths offsets nativeMask native_cap chainLabels native_inventory from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Supports
open private size negatives chainStart chainLength base newBase oldValue newValue chain_values from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private blocksWord blocksWord_flatMap from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open scoped BigOperators

private def bank (p : Parameters) (j : Fin 4) : List ℕ :=
  chainLabels p j 0 ++ chainLabels p j 1 ++ chainLabels p j 2 ++ chainLabels p j 3
private def terminal (p : Parameters) (chain : Fin 4) : ℕ := offsets p chain + lengths p chain
private def order : Fin 4 → Fin 4 := ![0,3,2,1]
private def blocks (p : Parameters) : List (List ℕ × ℕ) :=
  [(bank p 0,terminal p 0),(bank p 1,terminal p 3),
   (bank p 2,terminal p 2),(bank p 3,terminal p 1)]
private def word (p : Parameters) : List ℕ := blocksWord (blocks p)

private theorem physical_inventory (p : Parameters) : (word p).Perm (List.range (size p.a p.b p.c p.d)) := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  let C := chainLabels p
  have chain (r : Fin 4) :
      (C 0 r ++ C 1 r ++ C 2 r ++ C 3 r ++ [terminal p r]).Perm
        (List.range' (offsets p r) (lengths p r+1)) := by
    have h := (native_inventory p r).append_right [terminal p r]
    have he : List.range' (offsets p r) (lengths p r) ++ [terminal p r] =
        List.range' (offsets p r) (lengths p r+1) := by
      exact (List.range'_1_concat (s := offsets p r) (n := lengths p r)).symm
    simpa only [C,List.append_assoc,he] using h
  have hU := chain 0; have hV := chain 1; have hW := chain 2; have hX := chain 3
  have hpos (r : Fin 4) : lengths p r+1 = chainLength p.a p.b p.c p.d r := by
    fin_cases r <;> dsimp [lengths,chainLength] <;> omega
  rw [hpos] at hU hV hW hX
  have ranges : List.range' 0 p.d ++ List.range' p.d p.c ++
      List.range' (p.d+p.c) p.b ++ List.range' (p.d+p.c+p.b) p.a =
        List.range (size p.a p.b p.c p.d) := by
    have h0 := List.range'_append_1 (s := 0) (m := p.d) (n := p.c)
    have h1 := List.range'_append_1 (s := 0) (m := p.d+p.c) (n := p.b)
    have h2 := List.range'_append_1 (s := 0) (m := p.d+p.c+p.b) (n := p.a)
    simp only [Nat.zero_add] at h0 h1 h2
    rw [h0,h1,h2]
    simp [size,← List.range_eq_range',show p.d+p.c+p.b+p.a = p.a+p.b+p.c+p.d by omega]
  have regroup : (word p).Perm
      ((C 0 0 ++ C 1 0 ++ C 2 0 ++ C 3 0 ++ [terminal p 0]) ++
       (C 0 1 ++ C 1 1 ++ C 2 1 ++ C 3 1 ++ [terminal p 1]) ++
       (C 0 2 ++ C 1 2 ++ C 2 2 ++ C 3 2 ++ [terminal p 2]) ++
       (C 0 3 ++ C 1 3 ++ C 2 3 ++ C 3 3 ++ [terminal p 3])) := by
    apply Multiset.coe_eq_coe.mp
    simp only [word,blocks,blocksWord,bank,List.singleton_append,List.cons_append,List.nil_append]
    simp only [← Multiset.coe_add]
    dsimp only [C]
    ac_rfl
  apply regroup.trans
  have h := hU.append (hV.append (hW.append hX))
  simpa only [offsets,chainLength,← List.append_assoc,ranges] using h

private theorem positive_chain (p : Parameters) (j chain : Fin 4) (i : ℕ)
    (hi : i ∈ chainLabels p j chain) :
    i < size p.a p.b p.c p.d ∧ i ∉ negatives p.a p.b p.c p.d := by
  obtain ⟨e,he,_,hi⟩ := (chamberLabels_mem _ _ _ i).mp hi
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  fin_cases chain <;> dsimp [lengths,offsets] at he hi <;>
    simp only [negatives,List.mem_cons,List.mem_nil_iff,or_false,size] <;> omega

private theorem positive_bank (p : Parameters) (j : Fin 4) (i : ℕ) (hi : i ∈ bank p j) :
    i < size p.a p.b p.c p.d ∧ i ∉ negatives p.a p.b p.c p.d := by
  simp only [bank,List.mem_append] at hi
  have h0 := positive_chain p j 0 i
  have h1 := positive_chain p j 1 i
  have h2 := positive_chain p j 2 i
  have h3 := positive_chain p j 3 i
  tauto

private theorem blocks_nodup (p : Parameters) : ∀ b ∈ blocks p, b.1.Nodup := by
  have hnd := (physical_inventory p).nodup_iff.mpr (List.nodup_range (n := size p.a p.b p.c p.d))
  change (blocksWord (blocks p)).Nodup at hnd
  rw [blocksWord_flatMap] at hnd
  intro b hb
  exact (List.nodup_append.mp ((List.nodup_flatMap.mp hnd).1 b hb)).1

private theorem chain_mass (p : Parameters) (j chain : Fin 4) :
    ((chainLabels p j chain).map (oldValue p.a p.b p.c p.d)).sum =
      (nativeMask p j chain : ℤ)*base p.a p.b p.c p.d chain ∧
    ((chainLabels p j chain).map (newValue p.a p.b p.c p.d)).sum =
      (nativeMask p j chain : ℤ)*newBase p.a p.b p.c p.d chain := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  have hv := chain_values p.a p.b p.c p.d (by omega) (by omega) hc (by omega)
  have hidx (e : ℕ) (he : e < lengths p chain) :
      e < chainLength p.a p.b p.c p.d chain ∧ e+1 < chainLength p.a p.b p.c p.d chain := by
    fin_cases chain <;> dsimp [lengths,chainLength] at * <;> omega
  constructor
  · apply chamberLabels_sum _ _ _ (native_cap p j chain)
    intro e he
    have hf := hv.2.1 chain e (hidx e he).1
    simpa only [if_pos (hidx e he).2] using hf
  · apply chamberLabels_sum _ _ _ (native_cap p j chain)
    intro e he
    have hg := hv.2.2.1 chain e (hidx e he).1
    simpa only [if_pos (hidx e he).2] using hg

private theorem bank_masses (p : Parameters) (j : Fin 4) :
    ((bank p j).map (oldValue p.a p.b p.c p.d)).sum =
      ∑ chain : Fin 4, (nativeMask p j chain : ℤ)*base p.a p.b p.c p.d chain ∧
    ((bank p j).map (newValue p.a p.b p.c p.d)).sum =
      ∑ chain : Fin 4, (nativeMask p j chain : ℤ)*newBase p.a p.b p.c p.d chain := by
  constructor
  · simp only [bank,List.map_append,List.sum_append,(chain_mass p j _).1,Fin.sum_univ_succ]
    ring
  · simp only [bank,List.map_append,List.sum_append,(chain_mass p j _).2,Fin.sum_univ_succ]
    ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
