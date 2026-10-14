/- GID: D5/S1/Words/AdmissibleWords/FibonacciGrayPath
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FibonacciGrayPath
   mirror-E: none(waiver:unbounded-path-construction)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming, mathlib/module/Mathlib.Data.List.Chain]
   utility: none
   digest: Reflected Fibonacci words give distinct admissible one-bit paths in every dimension. -/
/-
proof_shape: hamming_cons: bind-only; consumers: gray_chain,
  D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.weight_cons
Escape audit unfinished for hamming_cons:
  https://github.com/the-omega-institute/trureturing/issues/16779
-/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.AdmissibleWords.FibonacciGrayPath

open D5.S1.Words.AdmissibleWords.AdmissibleCount

/-- Immutable reflected enumeration of the whole no-11 word space. -/
def gray : (d : Nat) → List (Fin d → Bool)
  | 0 => [Fin.elim0]
  | 1 => [fun _ => false, fun _ => true]
  | d + 2 => ((gray (d + 1)).reverse.map (Fin.cons false)) ++
      ((gray d).reverse.map (fun w => Fin.cons true (Fin.cons false w)))

private theorem gray_nonempty (d : Nat) : gray d ≠ [] := by
  induction d using Nat.twoStepInduction with
  | zero => simp [gray]
  | one => simp [gray]
  | more d ih ih1 =>
      simp [gray]
      exact fun h _ => ih1 h

private theorem cons_injective {d : Nat} (a : Bool) :
    Function.Injective (Fin.cons (α := fun _ => Bool) a : (Fin d → Bool) → (Fin (d+1) → Bool)) := by
  intro x y h
  simpa using congrArg Fin.tail h

private theorem gray_nodup (d : Nat) : (gray d).Nodup := by
  induction d using Nat.twoStepInduction with
  | zero => simp [gray]
  | one =>
      simp [gray]
      intro h; exact Bool.false_ne_true (congrFun h 0)
  | more d ih ih1 =>
      rw [gray, List.nodup_append]
      refine ⟨(List.nodup_map_iff (cons_injective false)).mpr (List.nodup_reverse.mpr ih1),
        (List.nodup_map_iff ((cons_injective true).comp (cons_injective false))).mpr (List.nodup_reverse.mpr ih), ?_⟩
      intro w hw v hv he
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hv
      have := congrFun he 0
      simpa using this

private theorem gray_complete (d : Nat) (w : Fin d → Bool) :
    w ∈ gray d ↔ Adm d w := by
  induction d using Nat.twoStepInduction with
  | zero =>
      have : w = Fin.elim0 := by funext i; exact Fin.elim0 i
      simp [gray, Adm, this]
  | one =>
      simp only [gray, Adm, iff_true, List.mem_cons, List.mem_singleton]
      cases hw : w 0 with
      | false => left; funext i; simpa only [Fin.eq_zero i] using hw
      | true => right; left; funext i; simpa only [Fin.eq_zero i] using hw
  | more d ih ih1 =>
      rw [gray, List.mem_append]
      simp only [List.mem_map, List.mem_reverse]
      constructor
      · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
        · exact (adm_cons_false _ _).mpr ((ih1 _).mp hv)
        · exact (admEquiv d).symm (Sum.inr ⟨v, (ih _).mp hv⟩) |>.property
      · intro hw
        have reconstruct : ((admEquiv d).symm ((admEquiv d) ⟨w, hw⟩)).val = w :=
          congrArg Subtype.val ((admEquiv d).left_inv ⟨w, hw⟩)
        cases hv : (admEquiv d) ⟨w, hw⟩ with
        | inl v => rw [hv] at reconstruct; exact Or.inl ⟨v.val, (ih1 _).mpr v.property, reconstruct⟩
        | inr v => rw [hv] at reconstruct; exact Or.inr ⟨v.val, (ih _).mpr v.property, reconstruct⟩

private theorem head_gray (d : Nat) :
    (gray (d + 1)).head? = (gray d).getLast?.map (Fin.cons false) := by
  cases d with
  | zero =>
      simp only [gray, List.head?_cons, List.getLast?_singleton, Option.map_some, Option.some.injEq]
      funext i
      refine Fin.cases rfl (fun j => Fin.elim0 j) i
  | succ d =>
      rw [gray, List.head?_append_of_ne_nil]
      · simp [List.head?_map, List.head?_reverse]
      · simpa using gray_nonempty (d+1)

theorem hamming_cons {d : Nat} (a b : Bool) (x y : Fin d → Bool) :
    hammingDist (Fin.cons (α := fun _ => Bool) a x)
      (Fin.cons (α := fun _ => Bool) b y) =
      (if a = b then 0 else 1) + hammingDist x y := by
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  by_cases h : a = b <;> simp [h]

private theorem gray_chain (d : Nat) :
    (gray d).IsChain (fun x y => hammingDist x y = 1) := by
  induction d using Nat.twoStepInduction with
  | zero => exact .singleton _
  | one =>
      simp [gray, List.isChain_cons_cons, hammingDist, Finset.univ_unique]
  | more d ih ih1 =>
      rw [gray]
      apply List.IsChain.append
      · apply List.isChain_map_of_isChain (R := fun x y => hammingDist x y = 1) _
          (fun x y h => ?_)
          (List.isChain_reverse.mpr (ih1.imp (fun x y h => by simpa [hammingDist_comm] using h)))
        simpa [hamming_cons] using h
      · apply List.isChain_map_of_isChain (R := fun x y => hammingDist x y = 1) _
          (fun x y h => ?_)
          (List.isChain_reverse.mpr (ih.imp (fun x y h => by simpa [hammingDist_comm] using h)))
        simpa [hamming_cons] using h
      · intro x hx y hy
        simp only [List.getLast?_map, List.getLast?_reverse, List.head?_map,
          List.head?_reverse, head_gray, Option.map_map, Function.comp_def] at hx hy
        obtain ⟨u, hu, rfl⟩ := Option.mem_map.mp hx
        obtain ⟨v, hv, rfl⟩ := Option.mem_map.mp hy
        have : u = v := Option.mem_unique hu hv
        subst v
        simp [hamming_cons]

private theorem gray_length (d : Nat) : (gray d).length = Nat.fib (d+2) := by
  classical
  let f : Fin (gray d).length → {w : Fin d → Bool // Adm d w} :=
    fun i => ⟨(gray d).get i, (gray_complete d _).mp (List.get_mem _ _)⟩
  have bij : Function.Bijective f := by
    constructor
    · intro i j h
      exact List.nodup_iff_injective_get.mp (gray_nodup d) (congrArg Subtype.val h)
    · intro w
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((gray_complete d w.val).mpr w.property)
      exact ⟨i, Subtype.ext hi⟩
  have := Fintype.card_congr (Equiv.ofBijective f bij)
  simpa [admissibleWord_card_eq_fib] using this

/-- A chosen finite initial segment; its dimension can be zero. -/
structure StagePath (d h : Nat) where
  word : Fin (h + 1) → (Fin d → Bool)
  admissible : ∀ i, Adm d (word i)
  injective : Function.Injective word
  consecutive : ∀ i : Fin h, hammingDist (word i.castSucc) (word i.succ) = 1

/-- Fibonacci capacity supplies a genuine one-bit stage path, without an
assumed path-existence premise or a prescribed endpoint. -/
theorem exists_stage_path (d h : Nat) (capacity : h + 1 ≤ Nat.fib (d+2)) :
    ∃ word : Fin (h+1) → (Fin d → Bool),
      (∀ i, Adm d (word i)) ∧ Function.Injective word ∧
      ∀ i : Fin h, hammingDist (word i.castSucc) (word i.succ) = 1 := by
  have size : h + 1 ≤ (gray d).length := by rwa [gray_length]
  let idx : Fin (h+1) → Fin (gray d).length := fun i => ⟨i.val, by omega⟩
  refine ⟨fun i => (gray d).get (idx i), ?_, ?_, ?_⟩
  · intro i
    exact (gray_complete d _).mp (List.get_mem _ _)
  · intro i j h
    have := List.nodup_iff_injective_get.mp (gray_nodup d) h
    apply Fin.ext
    simpa only [idx] using congrArg (fun k : Fin (gray d).length => k.val) this
  · intro i
    have adj := List.isChain_iff_getElem.mp (gray_chain d) i.val (by omega)
    simpa [idx, List.get_eq_getElem] using adj


end D5.S1.Words.AdmissibleWords.FibonacciGrayPath
