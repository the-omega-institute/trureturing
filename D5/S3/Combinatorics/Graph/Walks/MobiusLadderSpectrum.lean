/- GID: D5/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Circulant, mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic]
   utility: none
   digest: Native cubic circulants, their component coordinates and all positive well-covered powers. -/
import D5.S3.Combinatorics.Graph.Walks.BinaryRungSpectrum
import D5.S3.Combinatorics.Graph.Walks.FiniteDistancePower
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace CubicCirculant

open SimpleGraph Finset
open WellCoveredPowerCliqueProduct (IsMaximalIndep WellCovered power WCP)
open MatchingCliqueCycle (spectrum)
open BinaryRungSpectrum (Vertex graph closing forward)

noncomputable section

/-- The native antipodal circulant, including its four-vertex boundary. -/
def mobius (m : ℕ) : SimpleGraph (ZMod (2 * (m + 2))) :=
  circulantGraph ({1, ((m + 2 : ℕ) : ZMod (2 * (m + 2)))} : Set (ZMod (2 * (m + 2))))

/-- Rung coordinates retain the actual cyclic vertices: `(i,b)` represents `i + (m+2)b`. -/
def rungEquiv (m : ℕ) : Vertex m ≃ ZMod (2 * (m + 2)) :=
  (Equiv.prodComm _ _).trans finProdFinEquiv

theorem rungEquiv_val (m : ℕ) (x : Vertex m) :
    (rungEquiv m x).val = x.1.val + (m + 2) * x.2.val := rfl

private theorem rungEquiv_forward (m : ℕ) (x : Vertex m) :
    rungEquiv m (forward (closing m 1) x) = rungEquiv m x + 1 := by
  rcases x with ⟨i,b⟩
  have hib := i.isLt
  have hcases : ∀ b : ZMod 2, b=0 ∨ b=1 := by decide +kernel
  have htwo : (1 : ZMod 2)+1=0 := by decide +kernel
  have hi : (i+1).val = (i.val+1) % (m+2) := by simp [Fin.val_add]
  apply ZMod.val_injective
  rw [rungEquiv_val,ZMod.val_add,rungEquiv_val,ZMod.val_one_eq_one_mod]
  rw [Nat.mod_eq_of_lt (by omega : 1 < 2*(m+2))]
  change (i+1).val + (m+2)*(b+closing m 1 i).val =
    (i.val+(m+2)*b.val+1) % (2*(m+2))
  by_cases hl : i.val+1=m+2
  · have hindex : (i+1).val=0 := by rw [hi,hl,Nat.mod_self]
    rw [hindex]
    simp only [closing,hl,ite_true]
    rcases hcases b with rfl | rfl
    · simp only [zero_add,ZMod.val_zero,ZMod.val_one_eq_one_mod]
      norm_num
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [htwo,ZMod.val_zero,ZMod.val_one_eq_one_mod]
      norm_num
      have hn : i.val+(m+2)+1=2*(m+2) := by omega
      rw [hn,Nat.mod_self]
  · have hindex : (i+1).val=i.val+1 := by
      rw [hi,Nat.mod_eq_of_lt (by omega)]
    rw [hindex]
    simp only [closing,hl,ite_false,add_zero]
    rcases hcases b with rfl | rfl
    · rw [ZMod.val_zero]
      simp only [Nat.mul_zero,Nat.add_zero]
      rw [Nat.mod_eq_of_lt (by omega)]
    · rw [ZMod.val_one_eq_one_mod]
      norm_num
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

private def flip {m : ℕ} (x : Vertex m) : Vertex m := (x.1,x.2+1)

private theorem rungEquiv_flip (m : ℕ) (x : Vertex m) :
    rungEquiv m (flip x) = rungEquiv m x + ((m+2 : ℕ) : ZMod (2*(m+2))) := by
  rcases x with ⟨i,b⟩
  have hib := i.isLt
  have hcases : ∀ b : ZMod 2, b=0 ∨ b=1 := by decide +kernel
  have htwo : (1 : ZMod 2)+1=0 := by decide +kernel
  apply ZMod.val_injective
  rw [rungEquiv_val,ZMod.val_add,rungEquiv_val,
    ZMod.val_natCast_of_lt (by omega)]
  change i.val+(m+2)*(b+1).val = (i.val+(m+2)*b.val+(m+2)) % (2*(m+2))
  rcases hcases b with rfl | rfl
  · simp only [zero_add,ZMod.val_zero,ZMod.val_one_eq_one_mod]
    norm_num
    rw [Nat.mod_eq_of_lt (by omega)]
  · rw [htwo,ZMod.val_zero,ZMod.val_one_eq_one_mod]
    norm_num
    have hn : i.val+(m+2)+(m+2)=i.val+2*(m+2) := by omega
    rw [hn,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

/-- The cyclic matching graph is isomorphic to the actual Möbius circulant. -/
def mobiusIso (m : ℕ) : graph (closing m 1) ≃g mobius m where
  toEquiv := rungEquiv m
  map_rel_iff' := by
    intro x y
    have hhalf : ((m + 2 : ℕ) : ZMod (2 * (m + 2))) + ((m + 2 : ℕ) : ZMod (2 * (m + 2))) = 0 := by
      rw [← Nat.cast_add]
      convert ZMod.natCast_self (2 * (m + 2)) using 1 <;> congr 1 <;> omega
    have hrung : (x.1 = y.1 ∧ x ≠ y) ↔ flip x = y := by
      constructor
      · rintro ⟨hi,hne⟩
        have hb : x.2 ≠ y.2 := fun h => hne (Prod.ext hi h)
        have hval : y.2 = x.2+1 := by
          have hh : ∀ a b : ZMod 2, a ≠ b → b=a+1 := by decide +kernel
          exact hh x.2 y.2 hb
        exact Prod.ext hi hval.symm
      · intro h
        have hi : x.1 = y.1 := by
          simpa only [flip] using congrArg (fun z : Vertex m => z.1) h
        refine ⟨hi,?_⟩
        intro he
        have hb : x.2+1=x.2 := (congrArg Prod.snd h).trans (congrArg Prod.snd he).symm
        simpa using hb
    change (rungEquiv m x ≠ rungEquiv m y ∧
      ((rungEquiv m x-rungEquiv m y ∈ ({1,((m+2 : ℕ) : ZMod (2*(m+2)))} : Set (ZMod (2*(m+2))))) ∨
       (rungEquiv m y-rungEquiv m x ∈ ({1,((m+2 : ℕ) : ZMod (2*(m+2)))} : Set (ZMod (2*(m+2))))))) ↔
      ((x.1 = y.1 ∧ x ≠ y) ∨ forward (closing m 1) x = y ∨
        forward (closing m 1) y = x)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    rw [hrung]
    have hstep (u v : Vertex m) :
        rungEquiv m u-rungEquiv m v=1 ↔ forward (closing m 1) v=u := by
      rw [sub_eq_iff_eq_add',← rungEquiv_forward]
      constructor
      · intro h; exact ((rungEquiv m).injective h).symm
      · intro h; exact congrArg (rungEquiv m) h.symm
    have hflip (u v : Vertex m) :
        rungEquiv m u-rungEquiv m v=((m+2 : ℕ) : ZMod (2*(m+2))) ↔ flip v=u := by
      rw [sub_eq_iff_eq_add',← rungEquiv_flip]
      constructor
      · intro h; exact ((rungEquiv m).injective h).symm
      · intro h; exact congrArg (rungEquiv m) h.symm
    rw [hstep,hstep,hflip,hflip]
    have hff (z : Vertex m) : flip (flip z)=z := by
      apply Prod.ext
      · rfl
      · change (z.2+1)+1=z.2
        have ht : (1 : ZMod 2)+1=0 := by decide +kernel
        rw [add_assoc,ht,add_zero]
    have hfs : flip y=x ↔ flip x=y := by
      constructor
      · intro h; rw [← h,hff]
      · intro h; rw [← h,hff]
    rw [hfs]
    constructor
    · tauto
    · intro h
      refine ⟨?_,by tauto⟩
      intro he
      have hxy := (rungEquiv m).injective he
      subst y
      apply (graph (closing m 1)).irrefl
      change (x.1 = x.1 ∧ x ≠ x) ∨ forward (closing m 1) x = x ∨
        forward (closing m 1) x = x
      rcases h with hf | hstep | hstep
      · exact Or.inl (hrung.mpr hf)
      · exact Or.inr (Or.inl hstep)
      · exact Or.inr (Or.inr hstep)

/-- Full necessity and vertex-set attainability for every native Möbius ladder. -/
theorem mobius_spectrum (m k : ℕ) :
    k ∈ spectrum (mobius m) ↔ m+2 ≤ 2*k ∧ k ≤ m+2 ∧ Odd k := by
  rw [← FiniteDistancePower.spectrum_iso (mobiusIso m)]
  exact (BinaryRungSpectrum.closing_spectrum 1 k).trans
    (by rw [ZMod.natCast_eq_one_iff_odd])

end

end CubicCirculant
