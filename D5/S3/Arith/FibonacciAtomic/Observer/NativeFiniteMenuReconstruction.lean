/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuReconstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Prefix-closed native menu reconstruction preserves original rank and every future reply. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction

open GenealogicalFiberTransport (Source substitution decompose)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualImageAddressCertificate (height)
open NativeFiniteMenuCode

/-- Prefixes include the empty address and the selected address itself. -/
def PrefixClosed (S : Menu) : Prop :=
  ∀ q ∈ S, ∀ a : Address, a.IsPrefix q → a ∈ S

/-- This vector uses the given public list order, without sorting. -/
def initial (S : Menu) (u : Source) : List Reply := S.map (fun q => readout q u)

def future (S : Menu) (u : Source) (k : Nat) : List Reply :=
  initial S (substitution^[k] u)

/-- A leaf declaration must make every selected strict descendant absent. -/
def leafValid (S : Menu) (f : Address → Reply) : Bool :=
  S.all (fun q => q == [] || f q == .absent)

/-- Nonempty recursive menus reject an absent root; empty child menus need no data. -/
def reconstruct : Nat → Menu → (Address → Reply) → Option Source
  | 0, S, _ => if S = [] then some (.of true) else none
  | h + 1, S, f =>
    if S = [] then some (.of true) else
      match f [] with
      | .alpha => if leafValid S f then some (.of true) else none
      | .beta => if leafValid S f then some (.of false) else none
      | .absent => none
      | .branch => do
        let l ← reconstruct h (child false S) (fun r => f (false :: r))
        let r ← reconstruct h (child true S) (fun r => f (true :: r))
        some (.mul l r)

private theorem child_closed (S : Menu) (closed : PrefixClosed S) (b : Bool) :
    PrefixClosed (child b S) := by
  intro q hq a ha
  apply (mem_child b S a).mpr
  apply closed (b :: q) ((mem_child b S q).mp hq) (b :: a)
  rcases ha with ⟨z, rfl⟩
  exact ⟨z, rfl⟩

private theorem root_selected (S : Menu) (closed : PrefixClosed S) (hs : S ≠ []) :
    [] ∈ S := by
  cases S with
  | nil => contradiction
  | cons q S => exact closed q (by simp) [] List.nil_prefix

private theorem valid_leaf (S : Menu) (b : Bool) (f : Address → Reply)
    (agree : ∀ q ∈ S, f q = readout q (.of b)) : leafValid S f = true := by
  apply List.all_eq_true.mpr
  intro q hq
  rw [agree q hq]
  cases q <;> simp [readout]

/-- Every attained prefix-menu vector passes validation and produces one actual
representative with the original numerical code and all future selected replies. -/
theorem prefix_menu_reconstruction (h : Nat) (S : Menu) (u : Source)
    (f : Address → Reply) (closed : PrefixClosed S)
    (depth : ∀ q ∈ S, q.length < h) (agree : ∀ q ∈ S, f q = readout q u) :
    ∃ t : Source, reconstruct h S f = some t ∧ height t ≤ h ∧ code S t = code S u ∧
      ∀ q ∈ S, ∀ k : Nat, readout q (substitution^[k] t) = readout q (substitution^[k] u) := by
  induction h generalizing S u f with
  | zero =>
    have hs : S = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      have := depth q hq
      omega
    subst S
    exact ⟨.of true, by simp [reconstruct], by simp [height, decompose, BinaryTree.height],
      by simp [(original_code_grammar []).1 rfl], by simp⟩
  | succ h ih =>
    by_cases hs : S = []
    · subst S
      exact ⟨.of true, by simp [reconstruct], by simp [height, decompose, BinaryTree.height],
        by simp [(original_code_grammar []).1 rfl], by simp⟩
    · have hr := agree [] (root_selected S closed hs)
      cases u with
      | of b =>
        have hv := valid_leaf S b f agree
        refine ⟨.of b, ?_, ?_, rfl, ?_⟩
        · cases b <;> simp [reconstruct, hs, hr, readout, hv]
        · simp [height, decompose, BinaryTree.height]
        · intro q hq k; rfl
      | mul l r =>
        have childDepth (b : Bool) : ∀ q ∈ child b S, q.length < h := by
          intro q hq
          have hd := depth (b :: q) ((mem_child b S q).mp hq)
          simp only [List.length_cons] at hd
          omega
        obtain ⟨l', hl', hhl, hcl, hfl⟩ := ih (child false S) l
          (fun q => f (false :: q)) (child_closed S closed false) (childDepth false)
          (by intro q hq; exact agree (false :: q) ((mem_child false S q).mp hq))
        obtain ⟨r', hr', hhr, hcr, hfr⟩ := ih (child true S) r
          (fun q => f (true :: q)) (child_closed S closed true) (childDepth true)
          (by intro q hq; exact agree (true :: q) ((mem_child true S q).mp hq))
        refine ⟨.mul l' r', ?_, ?_, ?_, ?_⟩
        · simp [reconstruct, hs, hr, readout, hl', hr']
        · change max (height l') (height r') + 1 ≤ h + 1
          exact Nat.add_le_add_right (max_le hhl hhr) 1
        · rw [((original_code_grammar S).2.1 hs).2.1,
            ((original_code_grammar S).2.1 hs).2.1, hcl, hcr]
        · intro q hq k
          have iter (x y : Source) : substitution^[k] (.mul x y) =
              .mul (substitution^[k] x) (substitution^[k] y) :=
            Function.Semiconj₂.iterate (fun s t => substitution.map_mul s t) k x y
          rw [iter, iter]
          cases q with
          | nil => rfl
          | cons b q =>
            cases b
            · exact hfl q ((mem_child false S q).mpr hq) k
            · exact hfr q ((mem_child true S q).mpr hq) k

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction
