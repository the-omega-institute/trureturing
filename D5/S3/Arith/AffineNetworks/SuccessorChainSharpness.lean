/- GID: D5/S3/Arith/AffineNetworks/SuccessorChainSharpness
   generality: G
   mirror-B: D5/B/S3/Arith/AffineNetworks/SuccessorChainSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual named successor chains attain the original modular stopping depth. -/

import D5.S3.Arith.AffineNetworks.AffineModularStopping

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.AffineNetworks.SuccessorChainSharpness

open Quiver D5.S3.Arith.AffineNetworks.AffineModularStopping

universe u

/-- The attainer uses the original network, recurrence and phase run. The
prefix quantifiers include the empty prefix and every intermediate read. -/
theorem successor_chain_sharpness (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m) :
    ∃ (C : Network) (iv : C.V ≃ Fin N) (ie : C.E ≃ Fin (N - 1))
      (root last : C.V),
      C.m = m ∧ (iv root).val = 0 ∧ (iv last).val = N - 1 ∧
      (∀ e, (iv (C.src e)).val = (ie e).val ∧
        (iv (C.dst e)).val = (ie e).val + 1 ∧ C.a e = 1 ∧ C.c e = 0) ∧
      (∀ v, C.d v = if (iv v).val = N - 1 then m else 1) ∧
      (∀ n v, iterate C n v = if (iv v).val + n < N - 1 then 1 else m) ∧
      (∀ (v w : C.V) (p : NPath C v w),
        (iv w).val = (iv v).val + p.length ∧ ∀ t, pathRun p t = t) ∧
      (∀ (w : C.V) (p : NPath C root w), p.length < N - 1 →
        ∀ (u : C.V) (r : NPath C root u) (s : NPath C u w), p = r.comp s →
          C.d u = 1 ∧ portRead C u (pathRun r 0) = portRead C u (pathRun r 1)) ∧
      (∃ p : NPath C root last, p.length = N - 1 ∧
        (∀ t, (portRead C last (pathRun p t)).val = t.val) ∧
        portRead C last (pathRun p 0) ≠ portRead C last (pathRun p 1)) ∧
      (∀ n, n < N - 1 → iterate C n root = 1 ∧
        iterate C (N - 1) root = m ∧ iterate C n root ≠ iterate C (N - 1) root) ∧
      ∃ trace : ∀ {v w : C.V}, NPath C v w → ZMod C.m →
          List (C.E ⊕ (Σ v : C.V, ZMod (C.d v))),
        (∀ v t, trace (Path.nil : NPath C v v) t = [Sum.inr ⟨v, portRead C v t⟩]) ∧
        (∀ (v w x : C.V) (p : NPath C v w) (e : (networkQuiver C).Hom w x) t,
          trace (p.cons e) t = trace p t ++
            [Sum.inl e.1, Sum.inr ⟨x, portRead C x (pathRun (p.cons e) t)⟩]) ∧
        (∀ (w : C.V) (p : NPath C root w), p.length < N - 1 → trace p 0 = trace p 1) ∧
        ∀ (K : Type u)
          (choose : ∀ v : C.V, K → List (C.E ⊕ (Σ v : C.V, ZMod (C.d v))) →
            Option (Σ w : C.V, (networkQuiver C).Hom v w × K)),
          ∃ execute : ZMod C.m → K → ℕ → (Σ w : C.V, NPath C root w) × K,
            (∀ t k, execute t k 0 = (⟨root, Path.nil⟩, k)) ∧
            (∀ t k n, execute t k (n + 1) =
              let state := execute t k n
              match choose state.1.1 state.2 (trace state.1.2 t) with
              | none => state
              | some next => (⟨next.1, state.1.2.cons next.2.1⟩, next.2.2)) ∧
            (∀ t k n, (execute t k n).1.2.length ≤ n) ∧
            (∀ k n, n < N - 1 →
              execute 0 k n = execute 1 k n ∧
              trace (execute 0 k n).1.2 0 = trace (execute 1 k n).1.2 1 ∧
              HEq (choose (execute 0 k n).1.1 (execute 0 k n).2
                  (trace (execute 0 k n).1.2 0))
                (choose (execute 1 k n).1.1 (execute 1 k n).2
                  (trace (execute 1 k n).1.2 1))) := by
  classical
  let src : Fin (N - 1) → Fin N := fun e => ⟨e.val, by omega⟩
  let dst : Fin (N - 1) → Fin N := fun e => ⟨e.val + 1, by omega⟩
  let C : Network := {
    m := m, hm := by omega, V := Fin N,
    instV := inferInstance, instVDec := inferInstance,
    hV := ⟨⟨0, by omega⟩⟩, E := Fin (N - 1),
    instE := inferInstance, instEDec := inferInstance,
    src := src, dst := dst,
    d := fun v => if v.val = N - 1 then m else 1,
    hd := by intro v; split_ifs <;> simp_all; omega,
    a := fun _ => 1, c := fun _ => 0 }
  letI : Quiver C.V := networkQuiver C
  let root : C.V := ⟨0, by omega⟩
  let last : C.V := ⟨N - 1, by omega⟩
  have profile : ∀ n (v : C.V), iterate C n v =
      if v.val + n < N - 1 then 1 else m := by
    intro n
    induction n with
    | zero =>
        intro v
        change (if v.val = N - 1 then m else 1) = _
        split_ifs <;> omega
    | succ n ih =>
        intro v
        by_cases hv : v.val = N - 1
        · have hempty : (Finset.univ : Finset {e : C.E // C.src e = v}) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro e _
            have hs := congrArg Fin.val e.2
            change e.1.val = v.val at hs
            have he := e.1.isLt
            omega
          change Nat.lcm (if v.val = N - 1 then m else 1) _ = _
          rw [hempty]
          simp [hv]
        · have hlt : v.val < N - 1 := by have := v.isLt; omega
          let e : {e : C.E // C.src e = v} :=
            ⟨⟨v.val, hlt⟩, by apply Fin.ext; rfl⟩
          have hsingle : (Finset.univ : Finset {e : C.E // C.src e = v}) = {e} := by
            ext f
            simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
            apply Subtype.ext
            apply Fin.ext
            have hs := congrArg Fin.val f.2
            exact hs
          change Nat.lcm (if v.val = N - 1 then m else 1) _ = _
          rw [hsingle]
          simp only [hv, if_false, Finset.lcm_singleton]
          simp only [normalize_eq]
          change Nat.lcm 1 (iterate C n (dst e.1) / Nat.gcd (iterate C n (dst e.1)) 1) = _
          rw [Nat.gcd_one_right, Nat.div_one, Nat.lcm_one_left, ih]
          change (if v.val + 1 + n < N - 1 then 1 else m) = _
          simp only [Nat.add_assoc, Nat.add_comm 1 n]
  have rank : ∀ {v w : C.V} (p : NPath C v w), w.val = v.val + p.length := by
    intro v w p
    induction p with
    | nil => simp
    | @cons w x p e ih =>
        have hs := congrArg Fin.val e.2.1
        have ht := congrArg Fin.val e.2.2
        change e.1.val = w.val at hs
        change e.1.val + 1 = x.val at ht
        rw [Path.length_cons]
        omega
  have run : ∀ {v w : C.V} (p : NPath C v w) (t : ZMod C.m), pathRun p t = t := by
    intro v w p t
    induction p with
    | nil => rfl
    | cons p e ih => simpa [pathRun, C] using ih
  have reach : ∀ k (hk : k < N),
      ∃ p : NPath C root (⟨k, hk⟩ : C.V), p.length = k := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact ⟨Path.nil, rfl⟩
    | succ k ih =>
        intro hk
        obtain ⟨p, hp⟩ := ih (by omega)
        let e : (networkQuiver C).Hom (⟨k, by omega⟩ : C.V) (⟨k + 1, hk⟩ : C.V) :=
          ⟨⟨k, by omega⟩, by apply Fin.ext; rfl, by apply Fin.ext; rfl⟩
        exact ⟨p.cons e, by simp [hp]⟩
  have short : ∀ {w : C.V} (p : NPath C root w), p.length < N - 1 →
      C.d w = 1 := by
    intro w p hp
    have hr := rank p
    have hw : w.val ≠ N - 1 := by change w.val = 0 + p.length at hr; omega
    simp [C, hw]
  have equalRead : ∀ {w : C.V} (p : NPath C root w), p.length < N - 1 →
      portRead C w (pathRun p 0) = portRead C w (pathRun p 1) := by
    intro w p hp
    have hd := short p hp
    generalize portRead C w (pathRun p 0) = a
    generalize portRead C w (pathRun p 1) = b
    revert a b
    rw [hd]
    exact fun a b => Subsingleton.elim a b
  let trace : ∀ {v w : C.V}, NPath C v w → ZMod C.m →
      List (C.E ⊕ (Σ v : C.V, ZMod (C.d v))) := fun {v w} p t => by
    induction p with
    | nil => exact [Sum.inr ⟨v, portRead C v t⟩]
    | @cons w x p e ih => exact ih ++
        [Sum.inl e.1, Sum.inr ⟨x, portRead C x (pathRun (p.cons e) t)⟩]
  have sameTrace : ∀ {w : C.V} (p : NPath C root w), p.length < N - 1 →
      trace p 0 = trace p 1 := by
    intro w p
    induction p with
    | nil =>
        intro hp
        have h := equalRead (Path.nil : NPath C root root) hp
        change ([Sum.inr ⟨root, portRead C root 0⟩] :
          List (C.E ⊕ (Σ v : C.V, ZMod (C.d v)))) = [Sum.inr ⟨root, portRead C root 1⟩]
        change portRead C root 0 = portRead C root 1 at h
        rw [h]
    | @cons w x p e ih =>
        intro hp
        have hl : p.length < N - 1 := by rw [Path.length_cons] at hp; omega
        change trace p 0 ++ _ = trace p 1 ++ _
        rw [ih hl, equalRead (p.cons e) hp]
  obtain ⟨terminal, hterminal⟩ := reach (N - 1) (by omega)
  have terminalRead : ∀ t : ZMod C.m,
      (portRead C last (pathRun terminal t)).val = t.val := by
    intro t
    rw [run]
    have hd : C.d last = C.m := by simp [C, last]
    simp only [portRead, ZMod.castHom_apply]
    have hcast : ∀ d : ℕ, d = C.m → (ZMod.cast t : ZMod d).val = t.val := by
      intro d heq
      subst d
      rw [ZMod.cast_id]
    exact hcast (C.d last) hd
  have separate : portRead C last (pathRun terminal 0) ≠
      portRead C last (pathRun terminal 1) := by
    intro heq
    have hv := congrArg ZMod.val heq
    rw [terminalRead, terminalRead] at hv
    have hone : (1 : ZMod C.m).val = 1 := by
      change (1 : ZMod m).val = 1
      letI : Fact (1 < m) := ⟨by omega⟩
      exact ZMod.val_one m
    simp [hone] at hv
  refine ⟨C, Equiv.refl _, Equiv.refl _, root, last, rfl, rfl, rfl,
    ?_, ?_, profile, ?_, ?_, ⟨terminal, hterminal, terminalRead, separate⟩, ?_, ?_⟩
  · intro e; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro v; rfl
  · intro v w p; exact ⟨rank p, run p⟩
  · intro w p hp u r s heq
    have hl : r.length < N - 1 := by rw [heq, Path.length_comp] at hp; omega
    exact ⟨short r hl, equalRead r hl⟩
  · intro n hn
    have hzero : root.val = 0 := rfl
    rw [profile, profile]
    simp only [hzero, zero_add, hn, if_true, lt_self_iff_false, if_false]
    exact ⟨trivial, trivial, by omega⟩

  · refine ⟨@trace, ?_, ?_, ?_, ?_⟩
    · intro v t; rfl
    · intro v w x p e t; rfl
    · intro w p hp; exact sameTrace p hp
    · intro K choose
      let step (t : ZMod C.m) (state : (Σ w : C.V, NPath C root w) × K) :=
        match choose state.1.1 state.2 (trace state.1.2 t) with
        | none => state
        | some next => (⟨next.1, state.1.2.cons next.2.1⟩, next.2.2)
      let execute (t : ZMod C.m) (k : K) (n : ℕ) :
          (Σ w : C.V, NPath C root w) × K :=
        Nat.rec (⟨⟨root, Path.nil⟩, k⟩ : (Σ w : C.V, NPath C root w) × K)
          (fun _ state => step t state) n
      have lengthBound : ∀ t k n, (execute t k n).1.2.length ≤ n := by
        intro t k n
        induction n with
        | zero => simp [execute]
        | succ n ih =>
            dsimp only [execute, step]
            split
            · exact ih.trans (Nat.le_succ n)
            · simp only [Path.length_cons]
              exact Nat.succ_le_succ ih
      have coupled : ∀ k n, n < N - 1 → execute 0 k n = execute 1 k n := by
        intro k n
        induction n with
        | zero => intro _; rfl
        | succ n ih =>
            intro hn
            have hprior := ih (by omega)
            have ht := sameTrace (execute 1 k n).1.2
              (lt_of_le_of_lt (lengthBound 1 k n) (by omega))
            change step 0 (execute 0 k n) = step 1 (execute 1 k n)
            rw [hprior]
            simp only [step, ht]
      refine ⟨execute, ?_, ?_, lengthBound, ?_⟩
      · intro t k; rfl
      · intro t k n
        change step t (execute t k n) = _
        dsimp only [step]
        split <;> simp_all only
      · intro k n hn
        have hc := coupled k n hn
        have ht := sameTrace (execute 1 k n).1.2
          (lt_of_le_of_lt (lengthBound 1 k n) hn)
        refine ⟨hc, ?_, ?_⟩
        · rw [hc]; exact ht
        · rw [hc, ht]

end D5.S3.Arith.AffineNetworks.SuccessorChainSharpness
