import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.Range
import Mathlib.Logic.Function.Iterate

/-! An isolated probe of arXiv:2411.11914v2, Conjecture 6.2.
The dotted-pattern map is modeled by the proved right-hand side of Proposition 3.5.
No formal equivalence to the paper's original dotted-pattern stack is asserted. -/

namespace SyyProbe

/-- A valley is strictly smaller than every preceding entry. -/
def IsValley (earlier : List ℕ) (entry : ℕ) : Prop :=
  ∀ a ∈ earlier, entry < a

/-- The current valley starts a run, which ends just before the next smaller entry. -/
def valleyRuns : List ℕ → List (List ℕ)
  | [] => []
  | v :: tail =>
      (v :: tail.takeWhile (fun x => decide (v ≤ x))) ::
        valleyRuns (tail.dropWhile (fun x => decide (v ≤ x)))
termination_by w => w.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-- The Proposition 3.5 expression, used as the model's dotted-pattern map. -/
def r (w : List ℕ) : List ℕ := (valleyRuns w).map List.reverse |>.flatten

/-- Stack head is the top. Pop while top < current; push otherwise; flush at EOF. -/
private def westRun (stack input : List ℕ) : List ℕ :=
  match input, stack with
  | [], stack => stack
  | x :: xs, [] => westRun [x] xs
  | x :: xs, a :: rest =>
      if a < x then a :: westRun rest (x :: xs)
      else westRun (x :: a :: rest) xs
termination_by (input.length, stack.length)
decreasing_by all_goals simp_wf; omega

/-- West's deterministic stack-sorting map, defined by its stack algorithm. -/
def s (w : List ℕ) : List ℕ := westRun [] w

/-- The 21-dot machine, in the order specified by the source. -/
def M (w : List ℕ) : List ℕ := s (r w)

/-- The proposed potential, compared with the ordinary lexicographic order. -/
def Phi (w : List ℕ) : List ℕ := w.reverse

private theorem westRun_perm (stack input : List ℕ) :
    (westRun stack input).Perm (stack ++ input) := by
  fun_induction westRun stack input with
  | case1 stack => simp [westRun]
  | case2 x xs ih => simpa [westRun] using ih
  | case3 x xs a rest h ih => simpa [westRun, h] using ih.cons a
  | case4 x xs a rest h ih =>
      simpa [westRun, h] using ih.trans List.perm_middle.symm

private theorem westRun_sentinel (stack input : List ℕ) (m : ℕ)
    (bound : ∀ x ∈ input, x ≤ m) :
    westRun (stack ++ [m]) input = westRun stack input ++ [m] := by
  fun_induction westRun stack input with
  | case1 stack => simp [westRun]
  | case2 x xs ih =>
      have hx : ¬m < x := Nat.not_lt.mpr (bound x (by simp))
      have ht : ∀ y ∈ xs, y ≤ m := fun y hy => bound y (by simp [hy])
      simpa only [List.cons_append, List.nil_append, westRun, if_neg hx] using ih ht
  | case3 x xs a rest h ih =>
      simpa only [List.cons_append, westRun, if_pos h] using congrArg (a :: ·) (ih bound)
  | case4 x xs a rest h ih =>
      have ht : ∀ y ∈ xs, y ≤ m := fun y hy => bound y (by simp [hy])
      simpa only [List.cons_append, westRun, if_neg h] using ih ht

private theorem westRun_split (stack X Y : List ℕ) (m : ℕ)
    (hstack : ∀ x ∈ stack, x < m) (hX : ∀ x ∈ X, x < m) :
    westRun stack (X ++ m :: Y) = westRun stack X ++ westRun [m] Y := by
  fun_induction westRun stack X with
  | case1 stack =>
      simp only [List.nil_append, westRun]
      have drain : ∀ st : List ℕ, (∀ x ∈ st, x < m) →
          westRun st (m :: Y) = st ++ westRun [m] Y := by
        intro st
        induction st with
        | nil => intro _; simp only [westRun, List.nil_append]
        | cons a rest ih =>
            intro hs
            have ha := hs a (by simp)
            have hr : ∀ x ∈ rest, x < m := fun x hx => hs x (by simp [hx])
            simpa only [westRun, if_pos ha, List.cons_append] using
              congrArg (a :: ·) (ih hr)
      exact drain stack hstack
  | case2 x xs ih =>
      have hx := hX x (by simp)
      have ht : ∀ y ∈ xs, y < m := fun y hy => hX y (by simp [hy])
      simpa only [List.cons_append, westRun] using ih (by simpa using hx) ht
  | case3 x xs a rest h ih =>
      have hr : ∀ y ∈ rest, y < m := fun y hy => hstack y (by simp [hy])
      simpa only [List.cons_append, westRun, if_pos h] using
        congrArg (a :: ·) (ih hr hX)
  | case4 x xs a rest h ih =>
      have hx := hX x (by simp)
      have ht : ∀ y ∈ xs, y < m := fun y hy => hX y (by simp [hy])
      have hs : ∀ y ∈ x :: a :: rest, y < m := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hstack y hy
      simpa only [List.cons_append, westRun, if_neg h] using ih hs ht

private theorem s_split_max (X Y : List ℕ) (m : ℕ)
    (hX : ∀ x ∈ X, x < m) (hY : ∀ y ∈ Y, y ≤ m) :
    s (X ++ m :: Y) = s X ++ s Y ++ [m] := by
  rw [s, westRun_split [] X Y m (by simp) hX]
  have hs := westRun_sentinel [] Y m hY
  simpa only [List.nil_append, s, List.append_assoc] using
    congrArg (westRun [] X ++ ·) hs

private theorem r_perm (w : List ℕ) : (r w).Perm w := by
  fun_induction valleyRuns w with
  | case1 => simp [r, valleyRuns]
  | case2 v tail ih =>
      let p := fun x => decide (v ≤ x)
      have h := (List.reverse_perm (v :: tail.takeWhile p)).append ih
      simpa only [p, r, valleyRuns, List.map_cons, List.flatten_cons,
        List.cons_append, List.takeWhile_append_dropWhile] using h

private theorem s_ends_max (w : List ℕ) (ne : w ≠ []) :
    ∃ b m, s w = b ++ [m] ∧ m ∈ w ∧ ∀ x ∈ w, x ≤ m := by
  classical
  have hn : w.toFinset.Nonempty := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w ne
    exact ⟨a, by simpa using ha⟩
  obtain ⟨m, hm, hmax⟩ := w.toFinset.exists_max_image id hn
  have hm' : m ∈ w := by simpa using hm
  have bound : ∀ x ∈ w, x ≤ m := by simpa using hmax
  obtain ⟨X, Y, hw, hnX⟩ := List.eq_append_cons_of_mem hm'
  subst w
  have hx : ∀ x ∈ X, x < m := by
    intro x hmem
    have le := bound x (by simp [hmem])
    exact lt_of_le_of_ne le (fun e => hnX (e ▸ hmem))
  have hy : ∀ y ∈ Y, y ≤ m := fun y hmem => bound y (by simp [hmem])
  exact ⟨s X ++ s Y, m, s_split_max X Y m hx hy, hm', bound⟩

private theorem input_le_reverse_s (w : List ℕ) : w ≤ (s w).reverse := by
  induction w with
  | nil => simp [s, westRun]
  | cons a tail ih =>
      obtain ⟨b, m, hs, _, hmax⟩ := s_ends_max (a :: tail) (by simp)
      have ha := hmax a (by simp)
      rcases lt_or_eq_of_le ha with ha | rfl
      · rw [hs, List.reverse_append]
        exact le_of_lt (List.Lex.rel ha)
      · have hb : ∀ x ∈ tail, x ≤ a := fun x hx => hmax x (by simp [hx])
        have heq : s (a :: tail) = s tail ++ [a] := by
          simpa only [s, westRun, List.nil_append] using westRun_sentinel [] tail a hb
        rw [heq, List.reverse_append]
        exact List.cons_le_cons a ih

private theorem valleyRuns_append_valley (X Y : List ℕ) (v : ℕ)
    (bound : ∀ x ∈ X, v < x) :
    valleyRuns (X ++ v :: Y) = valleyRuns X ++ valleyRuns (v :: Y) := by
  fun_induction valleyRuns X with
  | case1 => simp [valleyRuns]
  | case2 a tail ih =>
      let p := fun x => decide (a ≤ x)
      have hv : p v = false := by simp [p, Nat.not_le.mpr (bound a (by simp))]
      have cut : ∀ t : List ℕ,
          (t ++ v :: Y).takeWhile p = t.takeWhile p ∧
          (t ++ v :: Y).dropWhile p = t.dropWhile p ++ v :: Y := by
        intro t
        induction t with
        | nil => simp [hv]
        | cons x xs ht =>
            cases hx : p x <;> simp [List.takeWhile_cons, List.dropWhile_cons, hx, ht]
      have hb : ∀ x ∈ tail.dropWhile p, v < x := by
        intro x hx
        have ht : x ∈ tail := List.dropWhile_subset p hx
        exact bound x (by simp [ht])
      simp only [valleyRuns, List.cons_append]
      rw [(cut tail).1, (cut tail).2, ih hb]
      rw [valleyRuns]

private theorem r_split_min (X Y : List ℕ) (v : ℕ)
    (hX : ∀ x ∈ X, v < x) (hY : ∀ y ∈ Y, v ≤ y) :
    r (X ++ v :: Y) = r X ++ Y.reverse ++ [v] := by
  have ht : Y.takeWhile (fun y => decide (v ≤ y)) = Y :=
    List.takeWhile_eq_self_iff.mpr (by simpa using hY)
  have hd : Y.dropWhile (fun y => decide (v ≤ y)) = [] :=
    List.dropWhile_eq_nil_iff.mpr (by simpa using hY)
  simp only [r, valleyRuns_append_valley X Y v hX, List.map_append,
    List.flatten_append, valleyRuns, ht, hd, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.reverse_cons,
    List.append_assoc]

private theorem append_le_of_length_eq {A B C D : List ℕ}
    (hlen : A.length = B.length) (hab : A ≤ B) (hcd : C ≤ D) :
    A ++ C ≤ B ++ D := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · have strict_extend {U V : List ℕ} (h : List.Lex (· < ·) U V) :
        ∀ C D : List ℕ, U.length = V.length →
          List.Lex (· < ·) (U ++ C) (V ++ D) := by
      induction h with
      | nil => intro C D hlen; simp at hlen
      | rel h => intro C D _; exact .rel h
      | cons h ih => intro C D hlen; exact .cons (ih C D (Nat.succ.inj hlen))
    exact le_of_lt (strict_extend hab C D hlen)
  · rcases lt_or_eq_of_le hcd with hcd | rfl
    · exact le_of_lt (List.Lex.append_left (· < ·) hcd A)
    · exact le_rfl

private theorem M_last_max (X A : List ℕ) (v m : ℕ)
    (hXmin : ∀ x ∈ X, v < x) (hAmin : ∀ a ∈ A, v ≤ a) (hvm : v ≤ m)
    (hXmax : ∀ x ∈ X, x < m) (hAmax : ∀ a ∈ A, a ≤ m) :
    M (X ++ v :: (A ++ [m])) = M X ++ s (A.reverse ++ [v]) ++ [m] := by
  have htail : ∀ y ∈ A ++ [m], v ≤ y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hAmin y hy
    · simpa using (List.mem_singleton.mp hy) ▸ hvm
  have hrX : ∀ x ∈ r X, x < m := fun x hx => hXmax x ((r_perm X).mem_iff.mp hx)
  have hrA : ∀ y ∈ A.reverse ++ [v], y ≤ m := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hAmax y (List.mem_reverse.mp hy)
    · simpa using (List.mem_singleton.mp hy) ▸ hvm
  unfold M
  rw [r_split_min X (A ++ [m]) v hXmin htail]
  simpa only [List.reverse_append, List.reverse_singleton, List.append_assoc,
    List.singleton_append, List.cons_append, List.nil_append] using s_split_max (r X) (A.reverse ++ [v]) m hrX hrA

private theorem potential_weak (w : List ℕ) (nd : w.Nodup) : Phi w ≤ Phi (M w) := by
  classical
  by_cases hw : w = []
  · subst w
    simp [Phi, M, r, valleyRuns, s, westRun]
  obtain ⟨W, a, rfl⟩ : ∃ W a, w = W ++ [a] :=
    ⟨w.dropLast, w.getLast hw, (List.dropLast_concat_getLast hw).symm⟩
  have hrne : r (W ++ [a]) ≠ [] := by
    intro he
    have hl := (r_perm (W ++ [a])).length_eq
    simp [he] at hl
  obtain ⟨b, m, hout, _, hb⟩ := s_ends_max (r (W ++ [a])) hrne
  have bound : ∀ x ∈ W ++ [a], x ≤ m :=
    fun x hx => hb x ((r_perm (W ++ [a])).mem_iff.mpr hx)
  have ha := bound a (by simp)
  rcases lt_or_eq_of_le ha with ha | he
  · change (W ++ [a]).reverse ≤ (s (r (W ++ [a]))).reverse
    rw [hout, List.reverse_append, List.reverse_append]
    exact le_of_lt (List.Lex.rel ha)
  · subst a
    by_cases hWnil : W = []
    · subst W
      simp [Phi, M, r, valleyRuns, s, westRun]
    have ndW : W.Nodup := (List.nodup_append.mp nd).1
    have notm : m ∉ W := by
      intro hm
      exact (List.nodup_append.mp nd).2.2 m hm m (by simp) rfl
    have maxW : ∀ x ∈ W, x < m := by
      intro x hx
      apply lt_of_le_of_ne (bound x (by simp [hx]))
      intro he
      subst x
      exact notm hx
    have hn : W.toFinset.Nonempty := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil W hWnil
      exact ⟨x, by simpa using hx⟩
    obtain ⟨v, hv, hmin⟩ := W.toFinset.exists_min_image id hn
    have hv' : v ∈ W := by simpa using hv
    have minW : ∀ x ∈ W, v ≤ x := by simpa using hmin
    obtain ⟨X, A, hWA, hvX⟩ := List.eq_append_cons_of_mem hv'
    subst W
    have hXmin : ∀ x ∈ X, v < x := by
      intro x hx
      apply lt_of_le_of_ne (minW x (by simp [hx]))
      intro he
      subst x
      exact hvX hx
    have hAmin : ∀ x ∈ A, v ≤ x := fun x hx => minW x (by simp [hx])
    have hXmax : ∀ x ∈ X, x < m := fun x hx => maxW x (by simp [hx])
    have hAmax : ∀ x ∈ A, x ≤ m := fun x hx => (maxW x (by simp [hx])).le
    have hvm : v ≤ m := (maxW v (by simp)).le
    have heq : M ((X ++ v :: A) ++ [m]) = M X ++ s (A.reverse ++ [v]) ++ [m] := by
      simpa only [List.append_assoc, List.cons_append] using
        M_last_max X A v m hXmin hAmin hvm hXmax hAmax
    have ndX := (List.nodup_append.mp ndW).1
    have hright := potential_weak X ndX
    have hleft := input_le_reverse_s (A.reverse ++ [v])
    have hlen : (A.reverse ++ [v]).length = (s (A.reverse ++ [v])).reverse.length := by
      simpa only [s, List.length_reverse, List.nil_append] using
        (westRun_perm [] (A.reverse ++ [v])).length_eq.symm
    have combined := append_le_of_length_eq hlen hleft hright
    change ((X ++ v :: A) ++ [m]).reverse ≤ (M ((X ++ v :: A) ++ [m])).reverse
    rw [heq]
    simpa only [List.reverse_append, List.reverse_cons, List.reverse_singleton,
      List.singleton_append, List.cons_append, List.append_assoc, List.reverse_nil,
      List.nil_append, Phi] using
        List.cons_le_cons m combined
termination_by w.length
decreasing_by
  simp_all only [List.length_append, List.length_cons, List.length_singleton]
  omega

/-- Shieh–Yang–Yu Conjecture 6.2 in its preregistered S_n form. -/
theorem result (n : ℕ) (_hn : 1 ≤ n) (w : List ℕ)
    (hw : w.Perm (List.range' 1 n)) :
    ∃ t : ℕ, (M^[t + 1]) w = (M^[t]) w := by
  classical
  have hnd : w.Nodup := hw.nodup_iff.mpr (List.nodup_range' 1)
  have permM (u : List ℕ) : (M u).Perm u := by
    have hs : (M u).Perm (r u) := by
      simpa only [M, s, List.nil_append] using westRun_perm [] (r u)
    exact hs.trans (r_perm u)
  have orbitperm : ∀ t : ℕ, ((M^[t]) w).Perm w := by
    intro t
    induction t with
    | zero => exact List.Perm.refl _
    | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact (permM _).trans ih
  let orbit := w.permutations.toFinset.filter (fun u => ∃ t : ℕ, (M^[t]) w = u)
  have memOrbit (t : ℕ) : (M^[t]) w ∈ orbit := by
    simp only [orbit, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
    exact ⟨orbitperm t, t, rfl⟩
  obtain ⟨u, hu, hmax⟩ := orbit.exists_max_image Phi ⟨w, by simpa using memOrbit 0⟩
  obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hu).2
  refine ⟨t, ?_⟩
  have hnext := hmax ((M^[t + 1]) w) (memOrbit (t + 1))
  rw [Function.iterate_succ_apply', ht] at hnext ⊢
  have ndu : u.Nodup := by
    rw [← ht]
    exact (orbitperm t).nodup_iff.mpr hnd
  have hwk := potential_weak u ndu
  have hPhi : Phi (M u) = Phi u := le_antisymm hnext hwk
  exact List.reverse_injective hPhi

#print axioms result

end SyyProbe
