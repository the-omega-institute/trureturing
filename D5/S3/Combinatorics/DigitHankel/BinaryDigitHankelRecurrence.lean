/- GID: D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence
   mirror-E: none(waiver:paired-binary-hankel-recurrence)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff]
   utility: none
   digest: Paired reflection recurrences for binary digit-sum Hankel determinants. -/

import D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelStructure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelRecurrence
open BinaryDigitHankelDefs
/-- The difference Hankel determinant with its final column replaced by ones. -/
def endpoint (n : ℕ) (t : ℤ) : ℤ :=
  (Matrix.of fun i j : Fin n => if (j:ℕ)+1<n then
    digitSum ((i:ℕ)+(j:ℕ)+1) t-digitSum ((i:ℕ)+(j:ℕ)) t else 1).det
/-- Binary-carry reflection gives the paired Hankel and endpoint recurrences. -/
theorem reflection (k n : ℕ) (t : ℤ) (hk : 1 ≤ k) (hn : 5 ≤ n)
    (hlo : 2^k < n) (hhi : n ≤ 3*2^(k-1)) :
    let m:=2^(k+1)-n+1
    let a:=2*n-2^(k+1)-1
    let u:=t^(k+1)-2*t^k
    hankel n t = (-1)^(n+1)*u^a*hankel m t+
      (t^k)^2*u^(a-1)*endpoint m t ∧
      endpoint n t=(-1)^n*u^a*endpoint m t := by
  classical
  have conjugate (k n : ℕ) (hpn : 2^k < n) (hshort : 2*(n-2^k-1)<2^k) (t : ℤ) :
      ∃ L : Matrix (Fin n) (Fin n) ℤ, L.det=1 ∧
        (∀ i : Fin n, (∑ j : Fin n,L i j) = if (i:ℕ)<2^k then 1 else 0) ∧
        ∀ i j : Fin n, (L * (Matrix.of fun i j : Fin n => digitSum (i+j) t) * L.transpose) i j =
        if (i:ℕ)<2^k then
          if (j:ℕ)<2^k then digitSum (i+j) t else
            if (j:ℕ)=2^k then t^k else
              (t^(k+1)-2*t^k)*(if 2^k≤(i:ℕ)+(j:ℕ)-2^k then 1 else 0)
        else if (i:ℕ)=2^k then
          if (j:ℕ)<2^k then t^k else if (j:ℕ)=2^k then t^(k+1)-2*t^k else 0
        else if (j:ℕ)<2^k then
          (t^(k+1)-2*t^k)*(if 2^k≤(i:ℕ)-2^k+(j:ℕ) then 1 else 0) else 0 := by
    have digitSum_block (k v u : ℕ) (t : ℤ) (hu : u < 2 ^ k) :
        digitSum (2 ^ k * v + u) t = t ^ k * digitSum v t + digitSum u t := by
      have shift (l : List ℤ) :
          (l.mapIdx fun j d => (d : ℤ) * t ^ (j + 1)).sum =
            t * (l.mapIdx fun j d => (d : ℤ) * t ^ j).sum := by
        have heq : (l.mapIdx fun j d => (d : ℤ) * t ^ (j + 1)) =
            (l.mapIdx fun j d => (d : ℤ) * t ^ j).map (fun z => t * z) := by
          apply List.ext_getElem
          · simp
          · intro i hi hi'
            simp only [List.getElem_map, List.getElem_mapIdx, pow_succ]; ring
        rw [heq, List.sum_map_mul_left]
        simp
      have step (a : ℕ) (e : ℕ) (he : e < 2) :
          digitSum (2 * a + e) t = (e : ℤ) + t * digitSum a t := by
        by_cases hz : a = 0 ∧ e = 0
        · rcases hz with ⟨rfl, rfl⟩
          simp [digitSum]
        · have hp : 0 < 2 * a + e := by omega
          unfold digitSum
          change ((List.flatMap (fun d : ℕ => [(d : ℤ)]) (Nat.digits 2 (2 * a + e))).mapIdx
            fun j d => d * t ^ j).sum =
              (e : ℤ) + t * ((List.flatMap (fun d : ℕ => [(d : ℤ)])
                (Nat.digits 2 a)).mapIdx fun j d => d * t ^ j).sum
          rw [← List.map_eq_flatMap, ← List.map_eq_flatMap]
          rw [Nat.digits_of_two_le_of_pos (by decide) hp]
          have hm : (2 * a + e) % 2 = e := by omega
          have hd : (2 * a + e) / 2 = a := by omega
          rw [hm, hd]; rw [List.map_cons, List.mapIdx_cons]
          simpa only [List.sum_cons, pow_zero, mul_one] using
            congrArg ((e : ℤ) + ·) (shift ((Nat.digits 2 a).map Nat.cast))
      induction k generalizing u with
      | zero =>
          have : u = 0 := by simpa using hu
          subst u
          simp [digitSum]
      | succ k ih =>
          have hu' : u / 2 < 2 ^ k := by rw [pow_succ] at hu; omega
          have he : u % 2 < 2 := Nat.mod_lt _ (by decide)
          have hsplit : 2 ^ (k + 1) * v + u =
              2 * (2 ^ k * v + u / 2) + u % 2 := by
            rw [pow_succ]
            calc
              2 ^ k * 2 * v + u = 2 * (2 ^ k * v) + u := by ring
              _ = 2 * (2 ^ k * v + u / 2) + u % 2 := by omega
          rw [hsplit, step _ _ he, ih _ hu']
          have huSplit : u = 2 * (u / 2) + u % 2 := by omega
          have huStep := step (u / 2) (u % 2) he
          rw [← huSplit] at huStep; rw [huStep, pow_succ]; ring
    have transform (n p : ℕ) (hp : 0 < p) (hpn : p < n) :
        ∃ L : Matrix (Fin n) (Fin n) ℤ, L.det = 1 ∧
          ∀ (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n),
          (L * M) i j = if (i : ℕ) < p then M i j else
            if (i : ℕ) = p then M i j - M ⟨0, by omega⟩ j else
              M i j - M ⟨(i:ℕ)-p, by omega⟩ j - M ⟨p, hpn⟩ j +
                M ⟨0, by omega⟩ j := by
      let z : Fin n := ⟨0, by omega⟩
      let P : Fin n := ⟨p, hpn⟩
      let d (i : Fin n) : Fin n := ⟨(i:ℕ)-p, by omega⟩
      let L : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
        if (i : ℕ) < p then (1 : Matrix (Fin n) (Fin n) ℤ) i j else
          if (i : ℕ) = p then (1 : Matrix (Fin n) (Fin n) ℤ) i j -
            (1 : Matrix (Fin n) (Fin n) ℤ) z j else
            (1 : Matrix (Fin n) (Fin n) ℤ) i j -
              (1 : Matrix (Fin n) (Fin n) ℤ) (d i) j -
              (1 : Matrix (Fin n) (Fin n) ℤ) P j +
              (1 : Matrix (Fin n) (Fin n) ℤ) z j
      have hdet : L.det = 1 := by
        have ht : L.IsLowerTriangular := by
          intro i j hij
          have hij' : (i : ℕ) < j := hij
          have hz : z ≠ j := by intro h; have := congrArg Fin.val h; dsimp [z] at this; omega
          have hd : d i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [d] at this; omega
          have hi : i ≠ j := ne_of_lt hij'
          dsimp [L]
          split_ifs with hl he
          · simp [Matrix.one_apply, hi]
          · simp [Matrix.one_apply, hi, hz]
          · have hP : P ≠ j := by
              intro h; have := congrArg Fin.val h; dsimp [P] at this; omega
            simp [Matrix.one_apply, hi, hz, hd, hP]
        rw [Matrix.det_of_isLowerTriangular L ht]
        have hdiag (i : Fin n) : L i i = 1 := by
          dsimp [L]
          split_ifs with hl he
          · simp
          · have hz : z ≠ i := by
              intro h; have := congrArg Fin.val h; dsimp [z] at this; omega
            simp [Matrix.one_apply, hz]
          · have hz : z ≠ i := by
              intro h; have := congrArg Fin.val h; dsimp [z] at this; omega
            have hd : d i ≠ i := by intro h; have := congrArg Fin.val h; dsimp [d] at this; omega
            have hP : P ≠ i := by intro h; have := congrArg Fin.val h; dsimp [P] at this; omega
            simp [Matrix.one_apply, hz, hd, hP]
        simp [hdiag]
      refine ⟨L, hdet, ?_⟩
      intro M i j
      change (L * M) i j = if (i:ℕ)<p then M i j else
        if (i:ℕ)=p then M i j-M z j else M i j-M (d i) j-M P j+M z j
      have hs (a : Fin n) : (∑ x : Fin n,
          (1 : Matrix (Fin n) (Fin n) ℤ) a x * M x j) = M a j := by
        change ((1 : Matrix (Fin n) (Fin n) ℤ) * M) a j = M a j; rw [Matrix.one_mul]
      rw [Matrix.mul_apply]
      dsimp [L]
      split_ifs with hl he
      · exact hs i
      · simp only [sub_mul, Finset.sum_sub_distrib, hs]
      · simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
    let p := 2^k
    have hp : 0<p := by dsimp [p]; positivity
    obtain ⟨L, hdet, hrow⟩ := transform n p hp hpn
    let A : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => digitSum (i+j) t
    have hsym : A.transpose = A := by ext i j; simp [A, Nat.add_comm]
    have hright (i j : Fin n) : (A*L.transpose) i j = (L*A) j i := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M j i)
        (Matrix.transpose_mul A L.transpose)
      simpa [hsym] using h
    have hinc (s : ℕ) (hs : s < 2*p) :
        digitSum (p+s) t = digitSum s t+t^k+
          (t^(k+1)-2*t^k)*(if p≤s then 1 else 0) := by
      by_cases hc : p≤s
      · have hr : s-p<p := by omega
        have h1 := digitSum_block k 2 (s-p) t hr
        have h2 := digitSum_block k 1 (s-p) t hr
        have he1 : 2^k*2+(s-p)=p+s := by dsimp [p] at *; omega
        have he2 : 2^k*1+(s-p)=s := by dsimp [p] at *; omega
        rw [he1] at h1; rw [he2] at h2
        have hd2 : digitSum 2 t=t := by change (0 : ℤ) * t^0 + (1*t^1+0)=t; ring
        have hd1 : digitSum 1 t=1 := by change (1 : ℤ) * t^0+0=1; ring
        rw [h1,h2,hd1,hd2,if_pos hc,pow_succ]; ring
      · have hr : s<2^k := by dsimp [p] at hc; omega
        have h := digitSum_block k 1 s t hr
        have hd1 : digitSum 1 t=1 := by change (1 : ℤ) * t^0+0=1; ring
        rw [show p+s=2^k*1+s by dsimp [p]; omega,h,hd1,if_neg hc]; ring
    have htwice (s : ℕ) (hs : s<p) : digitSum (2*p+s) t=t^(k+1)+digitSum s t := by
      have h := digitSum_block k 2 s t hs
      have hd2 : digitSum 2 t=t := by change (0 : ℤ) * t^0+(1*t^1+0)=t; ring
      rw [show 2*p+s=2^k*2+s by dsimp [p]; omega,h,hd2,pow_succ]
    have hlow (s : ℕ) (hs : s<p) : digitSum (p+s) t=digitSum s t+t^k := by
      rw [hinc _ (by omega)]
      simp [show ¬p≤s by omega]
    have hz : digitSum 0 t=0 := rfl
    have hpow : digitSum p t=t^k := by simpa [hz] using hlow 0 hp
    have h2pow : digitSum (2*p) t=t^(k+1) := by simpa [hz] using htwice 0 hp
    have hones (i : Fin n) : (∑ j : Fin n,L i j) = if (i:ℕ)<p then 1 else 0 := by
      let R : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun _ _ => 1
      have h := hrow R i ⟨0,by omega⟩
      simp only [R,Matrix.of_apply,sub_self,zero_sub,neg_add_cancel] at h
      simpa only [Matrix.mul_apply,Matrix.of_apply,mul_one,ite_self] using h
    refine ⟨L,hdet,hones,?_⟩
    intro i j
    change (L*A*L.transpose) i j =
      if (i:ℕ)<p then
        if (j:ℕ)<p then digitSum (i+j) t else
          if (j:ℕ)=p then t^k else
            (t^(k+1)-2*t^k)*(if p≤(i:ℕ)+(j:ℕ)-p then 1 else 0)
      else if (i:ℕ)=p then
        if (j:ℕ)<p then t^k else if (j:ℕ)=p then t^(k+1)-2*t^k else 0
      else if (j:ℕ)<p then
        (t^(k+1)-2*t^k)*(if p≤(i:ℕ)-p+(j:ℕ) then 1 else 0) else 0
    rw [Matrix.mul_assoc,hrow]; simp only [hright,hrow]
    by_cases hi : (i:ℕ)<p <;> by_cases hj : (j:ℕ)<p
    · simp [hi,hj,A,p,Nat.add_comm]
    · by_cases he : (j:ℕ)=p
      · have hjp : ¬(j:ℕ)<p := by omega
        simp only [hi,hjp,he,ite_true,ite_false]
        simp only [A,Matrix.of_apply,Fin.val_mk,Nat.zero_add]
        rw [show (j:ℕ)+(i:ℕ)=p+(i:ℕ) by omega, hinc _ (by omega)]
        simp [show ¬p≤(i:ℕ) by omega]
      · have hb : (j:ℕ)-p<p := by have := j.isLt; omega
        simp only [hi,hj,he,ite_true,ite_false,A,Matrix.of_apply,Fin.val_mk,Nat.zero_add]
        have hij : (j:ℕ)+(i:ℕ)=p+((j:ℕ)-p+(i:ℕ)) := by omega
        have hpi : p+(i:ℕ)<2*p := by omega
        rw [hij,hinc _ (by omega),hinc _ (show (i:ℕ)<2*p by omega)]
        have heq : (i:ℕ)+(j:ℕ)-p=(j:ℕ)-p+(i:ℕ) := by omega
        rw [heq]; simp only [show ¬p≤(i:ℕ) by omega,ite_false,mul_zero,add_zero]; ring
    · by_cases he : (i:ℕ)=p
      · simp only [hi,hj,he,ite_true,ite_false,A,Matrix.of_apply,Fin.val_mk,Nat.add_zero]
        rw [show (j:ℕ)+p=p+(j:ℕ) by omega,hinc _ (by omega)]
        simp [show ¬p≤(j:ℕ) by omega]
      · have hb : (i:ℕ)-p<p := by have := i.isLt; omega
        simp only [hi,hj,he,ite_true,ite_false,A,Matrix.of_apply,Fin.val_mk,Nat.add_zero]
        rw [show (j:ℕ)+(i:ℕ)=p+((i:ℕ)-p+(j:ℕ)) by omega,hinc _ (by omega),
          show (j:ℕ)+((i:ℕ)-p)=(i:ℕ)-p+(j:ℕ) by omega,
          show (j:ℕ)+p=p+(j:ℕ) by omega,hinc _ (by omega)]
        simp only [show ¬p≤(j:ℕ) by omega,ite_false,mul_zero,add_zero]; ring
    · have hb : (i:ℕ)-p<p := by have := i.isLt; omega
      have hc : (j:ℕ)-p<p := by have := j.isLt; omega
      have hbc : (i:ℕ)-p+((j:ℕ)-p)<p := by have := i.isLt; have := j.isLt; omega
      by_cases hei : (i:ℕ)=p <;> by_cases hej : (j:ℕ)=p
      · simp [hi,hj,hei,hej,A,hpow,h2pow,hz,show p+p=2*p by omega]
        ring
      · simp only [hi,hj,hei,hej,ite_true,ite_false,A,Matrix.of_apply,Fin.val_mk,
          Nat.add_zero,Nat.zero_add]
        rw [show (j:ℕ)+p=2*p+((j:ℕ)-p) by omega,htwice _ hc,
          show (j:ℕ)-p+p=(j:ℕ) by omega,
          show digitSum (j:ℕ) t=digitSum ((j:ℕ)-p) t+t^k from
            (by convert hlow _ hc using 1 <;> congr 1 <;> omega)]
        simp only [show p+p=2*p by omega,h2pow,hpow,hz,Nat.lt_irrefl,ite_false]; ring
      · simp only [hi,hj,hei,hej,ite_true,ite_false,A,Matrix.of_apply,Fin.val_mk,
          Nat.add_zero,Nat.zero_add]
        rw [show p+(i:ℕ)=2*p+((i:ℕ)-p) by omega,htwice _ hb,
          show p+((i:ℕ)-p)=(i:ℕ) by omega,
          show digitSum (i:ℕ) t=digitSum ((i:ℕ)-p) t+t^k from
            (by convert hlow _ hb using 1 <;> congr 1 <;> omega)]
        simp only [show p+p=2*p by omega,h2pow,hpow,hz,Nat.lt_irrefl,ite_false]; ring
      · simp only [hi,hj,hei,hej,ite_true,ite_false,A,Matrix.of_apply,Fin.val_mk,
          Nat.add_zero,Nat.zero_add]
        have hdj : digitSum (j:ℕ) t=digitSum ((j:ℕ)-p) t+t^k := by
          convert hlow _ hc using 1 <;> congr 1 <;> omega
        have hdi : digitSum (i:ℕ) t=digitSum ((i:ℕ)-p) t+t^k := by
          convert hlow _ hb using 1 <;> congr 1 <;> omega
        rw [show (j:ℕ)+(i:ℕ)=2*p+((i:ℕ)-p+((j:ℕ)-p)) by omega,htwice _ hbc,
          show (j:ℕ)-p+(i:ℕ)=p+((i:ℕ)-p+((j:ℕ)-p)) by omega,hlow _ hbc,
          show p+(i:ℕ)=2*p+((i:ℕ)-p) by omega,htwice _ hb,hdi,
          show (j:ℕ)+((i:ℕ)-p)=p+((i:ℕ)-p+((j:ℕ)-p)) by omega,hlow _ hbc,
          show (j:ℕ)-p+((i:ℕ)-p)=(i:ℕ)-p+((j:ℕ)-p) by omega,
          show p+((i:ℕ)-p)=(i:ℕ) by omega,hdi,
          show (j:ℕ)+p=2*p+((j:ℕ)-p) by omega,htwice _ hc,
          show (j:ℕ)-p+p=(j:ℕ) by omega,hdj,
          show p+p=2*p by omega,h2pow,hpow,hz]
        ring
  let p:=2^k
  let r:=n-p-1
  let m:=2*p-n+1
  let w:=t^k
  let u:=t^(k+1)-2*t^k
  let g:=fun z=>digitSum z t
  have hp : 0<p := by dsimp [p]; positivity
  have hpdouble : p=2*2^(k-1) := by
    calc
      p=2^((k-1)+1) := by dsimp [p]; congr 1; omega
      _=2*2^(k-1) := by rw [pow_succ]; ring
  have hsize : m+r+r+1=n := by dsimp [m,r]; omega
  have hmp : m+r=p := by dsimp [m,r]; omega
  have hpos : 0<m := by dsimp [m]; omega
  have hpn : m+r<n := by rw [hmp]; exact hlo
  have hshort : 2*(n-2^k-1)<2^k := by change 2*(n-p-1)<p; omega
  obtain ⟨L,hL,hones,hentries⟩ := conjugate k n hlo hshort t
  let A : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j=>digitSum (i+j) t
  let W:=L*A*L.transpose
  have hW : ∀ i j : Fin n, W i j =
      if (i:ℕ)<m+r then
        if (j:ℕ)<m+r then g ((i:ℕ)+(j:ℕ)) else
          if (j:ℕ)=m+r then w else
            u*(if m+r≤(i:ℕ)+(j:ℕ)-(m+r) then 1 else 0)
      else if (i:ℕ)=m+r then
        if (j:ℕ)<m+r then w else if (j:ℕ)=m+r then u else 0
      else if (j:ℕ)<m+r then
        u*(if m+r≤(i:ℕ)-(m+r)+(j:ℕ) then 1 else 0) else 0 := by
    intro i j
    simpa only [W,A,g,w,u,hmp,p] using hentries i j
  let e : Fin (m + 1) ⊕ (Fin r ⊕ Fin r) ≃ Fin n :=
    { toFun := fun a => match a with
        | Sum.inl i => if i.val < m then ⟨i.val, by omega⟩ else ⟨m + r, by omega⟩
        | Sum.inr (Sum.inl i) => ⟨m + i.val, by omega⟩
        | Sum.inr (Sum.inr i) => ⟨m + r + 1 + i.val, by omega⟩
      invFun := fun j =>
        if h₁ : j.val < m then Sum.inl ⟨j.val, by omega⟩
        else if h₂ : j.val < m + r then Sum.inr (Sum.inl ⟨j.val - m, by omega⟩)
        else if h₃ : j.val = m + r then Sum.inl (Fin.last m)
        else Sum.inr (Sum.inr ⟨j.val - (m + r + 1), by omega⟩)
      left_inv := by
        intro a
        rcases a with i | (i | i)
        · by_cases hi : i.val < m
          · simp [hi]
          · have he : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
            subst i
            have hp : ¬m + r < m := by omega
            simp [hp]
        · have h1 : ¬m + i.val < m := by omega
          have h2 : m + i.val < m + r := by omega
          simp [h1, h2]
        · have h1 : ¬m + r + 1 + i.val < m := by omega
          have h2 : ¬m + r + 1 + i.val < m + r := by omega
          have h3 : ¬m + r + 1 + i.val = m + r := by omega
          simp [h1, h2, h3]
      right_inv := by
        intro j
        dsimp only
        split_ifs with h1 h2 h3
        · simp [h1]
        · apply Fin.ext
          dsimp
          omega
        · simp only [Fin.val_last, lt_self_iff_false, if_false]
          exact Fin.ext h3.symm
        · apply Fin.ext
          dsimp
          omega }
  have forced (q : Type) [Fintype q] [DecidableEq q] (r : ℕ) (B : Matrix q q ℤ)
      (C : Matrix q (Fin r) ℤ) (C' : Matrix (Fin r) q ℤ)
      (D M : Matrix (Fin r) (Fin r) ℤ) (u : ℤ) :
      (fromBlocks B ((fun i => Sum.elim (C i) (fun _ => 0)))
        ((Matrix.of (Sum.elim (fun i j => C' i j) (fun _ _ => 0))))
        (fromBlocks D (u • M) (u • M.transpose) 0)).det =
        (-1) ^ r * u ^ (2 * r) * M.det ^ 2 * B.det := by
    let Q : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) ℤ := fromBlocks 0 1 1 0
    have hQ : Q.det = (-1) ^ r := by
      let P : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) ℤ := fromBlocks 1 1 0 1
      have hP : P.det = 1 := by simp [P, det_fromBlocks_zero₂₁]
      have hprod : P * Q = fromBlocks 1 1 1 0 := by simp [P, Q, fromBlocks_multiply]
      have hd := congrArg Matrix.det hprod
      rw [det_mul, hP, one_mul, det_fromBlocks_one₁₁] at hd
      simpa [Matrix.det_neg] using hd
    let A := fromBlocks B ((fun i => Sum.elim (C i) (fun _ => 0)))
      ((Matrix.of (Sum.elim (fun i j => C' i j) (fun _ _ => 0))))
      (fromBlocks D (u • M) (u • M.transpose) 0)
    let Q' : Matrix (q ⊕ (Fin r ⊕ Fin r)) (q ⊕ (Fin r ⊕ Fin r)) ℤ :=
      fromBlocks 1 0 0 Q
    have hQ' : Q'.det = (-1) ^ r := by simp [Q', det_fromBlocks_zero₂₁, hQ]
    have hprod : (A * Q').submatrix (Equiv.sumAssoc _ _ _)
        (Equiv.sumAssoc _ _ _) =
        fromBlocks (fromBlocks B 0 C' (u • M))
          ((Matrix.of (Sum.elim (fun i j => C i j) (fun i j => D i j))))
          0 (u • M.transpose) := by
      ext i j
      rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
        simp [A, Q', Q, Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply]
    have hd := congrArg Matrix.det hprod
    rw [det_submatrix_equiv_self, det_mul, hQ', det_fromBlocks_zero₂₁,
      det_fromBlocks_zero₁₂, det_smul, det_smul, det_transpose] at hd
    simp only [Fintype.card_fin] at hd
    have hs : (-1 : ℤ) ^ r * (-1) ^ r = 1 := by
      rw [← mul_pow]
      simp
    calc
      A.det = (-1)^r * (A.det * (-1)^r) := by rw [mul_left_comm, hs, mul_one]
      _ = (-1)^r * ((B.det * (u^r*M.det)) * (u^r*M.det)) := by rw [hd]
      _ = (-1)^r * u^(2*r) * M.det^2 * B.det := by rw [show 2*r = r+r by omega, pow_add]; ring
  let T := W.submatrix e e
  let B := T.submatrix Sum.inl Sum.inl
  let C := T.submatrix Sum.inl (Sum.inr ∘ Sum.inl)
  let C' := T.submatrix (Sum.inr ∘ Sum.inl) Sum.inl
  let D := T.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
  let M : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j =>
    if r≤(i:ℕ)+(j:ℕ)+1 then 1 else 0
  have hblock : T = fromBlocks B (fun i=>Sum.elim (C i) (fun _=>0))
      (Matrix.of (Sum.elim (fun i j=>C' i j) (fun _ _=>0)))
      (fromBlocks D (u•M) (u•M.transpose) 0) := by
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j)
    · rfl
    · rfl
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [T,e,Matrix.submatrix_apply,hW,Matrix.fromBlocks,
          show ¬m+r+1+(j:ℕ)<m+r by omega,
          show ¬m+r+1+(j:ℕ)=m+r by omega]
      · simp only [T,e,Matrix.submatrix_apply,Fin.val_castSucc,if_pos i.isLt,hW]
        simp [Matrix.fromBlocks,show (i:ℕ)<m+r by omega,
          show ¬m+r+1+(j:ℕ)<m+r by omega,
          show ¬m+r+1+(j:ℕ)=m+r by omega,
          show ¬m+r≤(i:ℕ)+(m+r+1+(j:ℕ))-(m+r) by omega]
    · rfl
    · rfl
    · change W ⟨m+(i:ℕ),by omega⟩ ⟨m+r+1+(j:ℕ),by omega⟩ =
        u*(if r≤(i:ℕ)+(j:ℕ)+1 then 1 else 0)
      rw [hW]
      have hi := i.isLt
      have hj := j.isLt
      simp only [Fin.val_mk,show m+(i:ℕ)<m+r by omega,
        show ¬m+r+1+(j:ℕ)<m+r by omega,
        show ¬m+r+1+(j:ℕ)=m+r by omega,ite_true,ite_false]
      congr 1
      apply if_congr
      · omega
      · rfl
      · rfl
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [T,e,Matrix.submatrix_apply,hW,Matrix.fromBlocks,
          show ¬m+r+1+(i:ℕ)<m+r by omega,
          show ¬m+r+1+(i:ℕ)=m+r by omega]
      · simp only [T,e,Matrix.submatrix_apply,Fin.val_castSucc,if_pos j.isLt,hW]
        simp [Matrix.fromBlocks,show (j:ℕ)<m+r by omega,
          show ¬m+r+1+(i:ℕ)<m+r by omega,
          show ¬m+r+1+(i:ℕ)=m+r by omega,
          show ¬m+r≤m+r+1+(i:ℕ)-(m+r)+(j:ℕ) by omega]
    · change W ⟨m+r+1+(i:ℕ),by omega⟩ ⟨m+(j:ℕ),by omega⟩ =
        u*(if r≤(j:ℕ)+(i:ℕ)+1 then 1 else 0)
      rw [hW]
      have hi := i.isLt
      have hj := j.isLt
      simp only [Fin.val_mk,show ¬m+r+1+(i:ℕ)<m+r by omega,
        show ¬m+r+1+(i:ℕ)=m+r by omega,
        show m+(j:ℕ)<m+r by omega,ite_true,ite_false]
      congr 1
      apply if_congr
      · omega
      · rfl
      · rfl
    · simp [T,e,Matrix.submatrix_apply,hW,Matrix.fromBlocks,
        show ¬m+r+1+(i:ℕ)<m+r by omega,
        show ¬m+r+1+(i:ℕ)=m+r by omega,
        show ¬m+r+1+(j:ℕ)<m+r by omega]
  have hB : B = Matrix.of fun i j : Fin (m+1) =>
      Fin.lastCases (Fin.lastCases u (fun _=>w) j)
        (fun i=>Fin.lastCases w (fun j=>g ((i:ℕ)+(j:ℕ))) j) i := by
    ext i j
    refine Fin.lastCases ?_ (fun i=>?_) i
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · simp [B,T,e,Matrix.submatrix_apply,hW]
      · simp [B,T,e,Matrix.submatrix_apply,hW,show (j:ℕ)<m+r by omega]
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · simp [B,T,e,Matrix.submatrix_apply,hW,show (i:ℕ)<m+r by omega]
      · simp [B,T,e,Matrix.submatrix_apply,hW,
          show (i:ℕ)<m+r by omega,show (j:ℕ)<m+r by omega]
  have hsquare : M.det^2=1 := by
    let T' := M.submatrix (Equiv.refl (Fin r)) Fin.revPerm
    have ht : T'.IsLowerTriangular := by
      intro i j hij
      change (if r ≤ i.val + j.rev.val + 1 then (1 : ℤ) else 0) = 0; rw [Fin.val_rev]
      have hij' : i.val < j.val := hij
      have hj := j.isLt
      rw [if_neg (by omega)]
    have hdiag (i : Fin r) : T' i i = 1 := by
      change (if r ≤ i.val + i.rev.val + 1 then (1 : ℤ) else 0) = 1; rw [Fin.val_rev]
      have hi := i.isLt
      rw [if_pos (by omega)]
    have hdet : T'.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular T' ht]
      simp [hdiag]
    have habs : |M.det| = 1 := by
      have h := Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl (Fin r))
        Fin.revPerm M
      change |T'.det| = |M.det| at h; rw [hdet] at h
      simpa using h.symm
    rw [← sq_abs, habs]; norm_num
  let v : Matrix (Fin (m+1)) Unit ℤ := fun i _ => if i.val < m then 1 else 0
  let v' : Matrix (Fin (m+1) ⊕ (Fin r ⊕ Fin r)) Unit ℤ :=
    fun i j => Sum.elim (fun i => v i j) (Sum.elim (fun _ => 1) (fun _ => 0)) i
  let o : Matrix (Fin n) Unit ℤ := fun _ _ => 1
  have hext : (fromBlocks A o o.transpose 0).det =
      (fromBlocks T v' v'.transpose 0).det := by
    let U : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℤ := fromBlocks L 0 0 1
    have hU : U.det = 1 := by simp [U, det_fromBlocks_zero₂₁, hL]
    have hp : U * fromBlocks A o o.transpose 0 * U.transpose =
        fromBlocks W (L * o) (L * o).transpose 0 := by
      simp [U, W, fromBlocks_multiply, fromBlocks_transpose, transpose_mul]
    have hd := congrArg Matrix.det hp
    rw [det_mul, det_mul, det_transpose, hU] at hd; simp only [one_mul, mul_one] at hd
    rw [hd, ← det_submatrix_equiv_self (Equiv.sumCongr e (Equiv.refl Unit))]
    congr 1
    have hv : ∀ i j, (L * o) (e i) j = v' i j := by
      intro i j
      simp only [Matrix.mul_apply, o, mul_one, hones]
      change (if (e i : ℕ) < p then (1 : ℤ) else 0) = v' i j
      rcases i with i | (i | i)
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [e,v',v,show ¬m+r<p by omega]
        · simp [e,v',v,show (i:ℕ)<p by omega]
      · simp [e,v',show m+(i:ℕ)<p by omega]
      · simp [e,v',show ¬m+r+1+(i:ℕ)<p by omega]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · exact hv i j
    · exact hv j i
    · rfl
  have hEcore : (fromBlocks A o o.transpose 0).det =
      (-1)^r*u^(2*r)*(fromBlocks B v v.transpose 0).det := by
    rw [hext]
    let f : ((Fin (m+1) ⊕ Unit) ⊕ (Fin r ⊕ Fin r)) ≃
        ((Fin (m+1) ⊕ (Fin r ⊕ Fin r)) ⊕ Unit) :=
      (Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
          (Equiv.sumAssoc _ _ _).symm)
    rw [← det_submatrix_equiv_self f]
    have hb : (fromBlocks T v' v'.transpose 0).submatrix f f =
        fromBlocks (fromBlocks B v v.transpose 0)
          (fun i => Sum.elim (Sum.elim (C ·) (fun _ _ => 1) i) (fun _ => 0))
          (Matrix.of (Sum.elim
            (fun i j => Sum.elim (C' i) (fun _ => 1) j) (fun _ _ => 0)))
          (fromBlocks D (u • M) (u • M.transpose) 0) := by
      rw [hblock]
      ext i j
      rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
        simp [v',f,Matrix.submatrix,Matrix.fromBlocks,Matrix.transpose]
    rw [hb,forced,hsquare,mul_one]
  have hHcore : hankel n t=(-1)^r*u^(2*r)*B.det := by
    have hdetW : W.det=hankel n t := by
      simp only [W,Matrix.det_mul,Matrix.det_transpose,hL,one_mul,mul_one]; rfl
    rw [← hdetW,← Matrix.det_submatrix_equiv_self e W]
    change T.det = _; rw [hblock,forced,hsquare,mul_one]
  have border (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (w u : ℤ) :
      let B : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ := fun i j =>
        Fin.lastCases (Fin.lastCases u (fun _ => w) j)
          (fun i => Fin.lastCases w (fun j => A i j) j) i
      let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := fun i j =>
        Fin.lastCases 1 (fun j => A i j.succ - A i j.castSucc) j
      B.det = u * A.det + (-1) ^ (n + 1) * w ^ 2 * Q.det := by
    intro B Q
    let C : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ := fun i j =>
      Fin.cases (B i 0) (fun j =>
        if j = Fin.last n then B i j.succ else B i j.succ - B i j.castSucc) j
    have hBC : B.det = C.det := by
      apply Matrix.det_eq_of_forall_col_eq_smul_add_pred
        (fun j => if j = Fin.last n then 0 else 1)
      · intro i
        simp [C]
      · intro i j
        simp only [C, Fin.cases_succ]
        split_ifs <;> ring
    have lc0 : Fin.lastCases u (fun _ : Fin (n + 1) => w) (0 : Fin (n + 2)) = w := by
      change Fin.lastCases u (fun _ : Fin (n + 1) => w) (0 : Fin (n + 1)).castSucc = w
      exact Fin.lastCases_castSucc 0
    have row0 : C (Fin.last (n + 1)) 0 = w := by simp [C, B, lc0]
    have rows (j : Fin (n + 1)) :
        C (Fin.last (n + 1)) j.succ = if j = Fin.last n then u else 0 := by
      simp only [C, Fin.cases_succ]
      split_ifs with h
      · subst j
        simp [B]
      · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr h
        simp [B, ← Fin.castSucc_succ]
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := fun i j =>
      Fin.cases (A i 0) (fun j => A i j.succ - A i j.castSucc) j
    have hKA : A.det = K.det := by
      apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (fun _ => 1)
      · intro i
        simp [K]
      · intro i j
        simp only [K, Fin.cases_succ]; ring
    have minorLast : (C.submatrix (Fin.last (n + 1)).succAbove
        (Fin.last (n + 1)).succAbove).det = A.det := by
      rw [hKA]
      congr 1
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last]
      change C i.castSucc j.castSucc = K i j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.castSucc_zero, C, Fin.cases_zero, B, Fin.lastCases_castSucc, K]
        change Fin.lastCases w (fun j => A i j) (0 : Fin (n + 1)).castSucc = A i 0
        exact Fin.lastCases_castSucc 0
      · simp only [Fin.castSucc_succ, C, Fin.cases_succ, K]
        simp [B, ← Fin.castSucc_succ]
    have minorZero : (C.submatrix (Fin.last (n + 1)).succAbove
        (0 : Fin (n + 2)).succAbove).det = w * Q.det := by
      have heq : C.submatrix (Fin.last (n + 1)).succAbove
          (0 : Fin (n + 2)).succAbove = Matrix.updateCol Q (Fin.last n) (fun _ => w) := by
        ext i j
        simp only [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_zero]
        change C i.castSucc j.succ = (Matrix.updateCol Q (Fin.last n) (fun _ => w)) i j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simp only [C, Fin.cases_succ]
          simp [B, Matrix.updateCol]
        · simp only [C, Fin.cases_succ]
          simp [B, Q, Matrix.updateCol, ← Fin.castSucc_succ]
      rw [heq]
      have hw : (fun _ : Fin (n + 1) => w) = w • (fun _ => (1 : ℤ)) := by
        ext
        simp
      rw [hw, Matrix.det_updateCol_smul]
      congr 1
      have hQ : Matrix.updateCol Q (Fin.last n) (fun _ => (1 : ℤ)) = Q := by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Q, Matrix.updateCol]
      rw [hQ]
    rw [hBC, Matrix.det_succ_row C (Fin.last (n + 1)), Fin.sum_univ_succ]
    simp only [Fin.val_last, Fin.val_zero, Nat.add_zero, row0, minorZero]
    have hs : (∑ j : Fin (n + 1),
        (-1 : ℤ) ^ (n + 1 + j.succ.val) *
          C (Fin.last (n + 1)) j.succ *
          (C.submatrix (Fin.last (n + 1)).succAbove j.succ.succAbove).det) =
        u * A.det := by
      rw [Finset.sum_eq_single (Fin.last n)]
      · simp only [rows, if_true, Fin.val_last, Fin.val_succ]
        have hs : (-1 : ℤ) ^ (n + 1 + (n + 1)) = 1 := by
          rw [show n + 1 + (n + 1) = 2 * (n + 1) by omega, pow_mul]; norm_num
        rw [hs, one_mul]
        simpa only [Fin.succ_last] using congrArg (u * ·) minorLast
      · intro j hj hjlast
        rw [rows, if_neg hjlast, mul_zero, zero_mul]
      · simp
    rw [hs]; ring
  have fixedBorder (m : ℕ) (hm : 0 < m) (w u t : ℤ) :
      let B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := fun i j =>
        Fin.lastCases (Fin.lastCases u (fun _ => w) j)
          (fun i => Fin.lastCases w (fun j => digitSum (i.val + j.val) t) j) i
      B.det = u * hankel m t + (-1) ^ m * w ^ 2 * endpoint m t := by
    intro B
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have h := border n (Matrix.of fun i j : Fin (n + 1) => digitSum (i.val + j.val) t) w u
    dsimp only at h
    have hQ : (fun i j : Fin (n + 1) =>
        Fin.lastCases 1 (fun j => digitSum (i.val + j.succ.val) t -
          digitSum (i.val + j.castSucc.val) t) j) =
        Matrix.of (fun i j : Fin (n + 1) => if j.val + 1 < n + 1 then
          digitSum (i.val + j.val + 1) t - digitSum (i.val + j.val) t else 1) := by
      ext i j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp only [Fin.lastCases_castSucc, Matrix.of_apply, Fin.val_castSucc, Fin.val_succ]
        rw [if_pos (by omega)]
        congr 2
    simp only [Matrix.of_apply] at h; rw [hQ] at h
    exact h
  let eps (m : ℕ) : Fin m ⊕ Unit ≃ Fin (m + 1) :=
    { toFun := Sum.elim Fin.castSucc (fun _ => Fin.last m)
      invFun := Fin.lastCases (Sum.inr ()) Sum.inl
      left_inv := by rintro (i | ⟨⟩) <;> simp
      right_inv := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }
  have extra (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ) (w u : ℤ) :
      let B : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) ℤ :=
        Matrix.fromBlocks A (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => 1) 0
      let C : Matrix (Fin m ⊕ Unit) Unit ℤ := fun i _ => Sum.elim (fun _ => w) (fun _ => 0) i
      (Matrix.fromBlocks B C C.transpose (Matrix.of fun _ _ : Unit => u)).det = u * B.det := by
    intro B C
    let R := Matrix.fromBlocks B C C.transpose (Matrix.of fun _ _ : Unit => u)
    have h := Matrix.det_updateRow_add_smul_self R
      (i := Sum.inr ()) (j := Sum.inl (Sum.inr ())) (by simp) (-w)
    have heq : R.updateRow (Sum.inr ())
        (fun j => R (Sum.inr ()) j + (-w) * R (Sum.inl (Sum.inr ())) j) =
        Matrix.fromBlocks B C 0 (Matrix.of fun _ _ : Unit => u) := by
      ext i j
      rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
        simp [R, B, C, Matrix.updateRow, Function.update, Matrix.fromBlocks]
    change (R.updateRow (Sum.inr ())
      (fun j => R (Sum.inr ()) j + (-w) * R (Sum.inl (Sum.inr ())) j)).det = R.det at h
    rw [heq, Matrix.det_fromBlocks_zero₂₁] at h
    have hu : (Matrix.of fun _ _ : Unit => u).det = u := by rw [Matrix.det_unique]; rfl
    rw [hu] at h
    change R.det = u * B.det; rw [← h]; ring
  have double (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ) (w u : ℤ) :
      let H := fromBlocks A (Matrix.of fun (_ : Fin m) (_ : Unit) => w)
        (Matrix.of fun _ : Unit => fun _ => w) (Matrix.of fun _ _ : Unit => u)
      let v : Matrix (Fin m ⊕ Unit) Unit ℤ :=
        fun i _ => Sum.elim (fun _ => 1) (fun _ => 0) i
      (fromBlocks H v v.transpose 0).det =
        u * (fromBlocks A (Matrix.of fun _ _ => (1 : ℤ))
          (Matrix.of fun _ _ => (1 : ℤ)) (0 : Matrix Unit Unit ℤ)).det := by
    intro H v
    let B : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) ℤ :=
      fromBlocks A (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => 1) 0
    let C : Matrix (Fin m ⊕ Unit) Unit ℤ :=
      fun i _ => Sum.elim (fun _ => w) (fun _ => 0) i
    let e : ((Fin m ⊕ Unit) ⊕ Unit) ≃ ((Fin m ⊕ Unit) ⊕ Unit) :=
      (Equiv.sumAssoc (Fin m) Unit Unit).trans
        ((Equiv.sumCongr (Equiv.refl (Fin m)) (Equiv.sumComm Unit Unit)).trans
          (Equiv.sumAssoc (Fin m) Unit Unit).symm)
    have heq : (fromBlocks H v v.transpose 0).submatrix e e =
        fromBlocks B C C.transpose (Matrix.of fun _ _ : Unit => u) := by
      ext i j
      rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
        simp [H, v, B, C, e, Matrix.submatrix, Matrix.fromBlocks, Matrix.transpose]
    have hd := congrArg Matrix.det heq
    rw [Matrix.det_submatrix_equiv_self] at hd; rw [hd]
    exact extra m A w u
  have concreteCore (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ) (w u : ℤ) :
      let B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := fun i j =>
        Fin.lastCases (Fin.lastCases u (fun _ => w) j)
          (fun i => Fin.lastCases w (fun j => A i j) j) i
      let v : Matrix (Fin (m + 1)) Unit ℤ :=
        fun i _ => Fin.lastCases 0 (fun _ => 1) i
      (fromBlocks B v v.transpose 0).det =
        u * (fromBlocks A (Matrix.of fun _ _ => (1 : ℤ))
          (Matrix.of fun _ _ => (1 : ℤ)) (0 : Matrix Unit Unit ℤ)).det := by
    intro B v
    let e := Equiv.sumCongr (eps m) (Equiv.refl Unit)
    have heq : (fromBlocks B v v.transpose 0).submatrix e e =
        fromBlocks
          (fromBlocks A (Matrix.of fun (_ : Fin m) (_ : Unit) => w)
            (Matrix.of fun _ : Unit => fun _ => w) (Matrix.of fun _ _ : Unit => u))
          (fun i (_ : Unit) => Sum.elim (fun _ => (1 : ℤ)) (fun _ => 0) i)
          (fun (_ : Unit) i => Sum.elim (fun _ => (1 : ℤ)) (fun _ => 0) i) 0 := by
      ext i j
      rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
        simp [B, v, e, eps, Matrix.submatrix, Matrix.fromBlocks, Matrix.transpose]
    have hd := congrArg Matrix.det heq
    rw [Matrix.det_submatrix_equiv_self] at hd; rw [hd]
    exact double m A w u
  have sumBorder (m : ℕ) (hm : 0<m) (t : ℤ) :
      (fromBlocks (Matrix.of fun i j : Fin m=>digitSum (i.val+j.val) t)
        (Matrix.of fun (_ : Fin m) (_ : Unit) => (1:ℤ))
        (Matrix.of fun _ : Unit=>fun _ : Fin m=>(1:ℤ)) (0:Matrix Unit Unit ℤ)).det=
        (-1)^m*(Matrix.of fun i j : Fin m=>if j.val+1<m then
          digitSum (i.val+j.val+1) t -digitSum (i.val+j.val) t else 1).det := by
    let B : Matrix (Fin (m+1)) (Fin (m+1)) ℤ := fun i j =>
      Fin.lastCases (Fin.lastCases 0 (fun _=>1) j)
        (fun i=>Fin.lastCases 1 (fun j=>digitSum (i.val+j.val) t) j) i
    have heq : B.submatrix (eps m) (eps m) = fromBlocks
        (Matrix.of fun i j : Fin m=>digitSum (i.val+j.val) t)
        (Matrix.of fun (_ : Fin m) (_ : Unit)=>(1:ℤ))
        (Matrix.of fun _ : Unit=>fun _ : Fin m=>(1:ℤ)) (0:Matrix Unit Unit ℤ) := by
      ext i j
      rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
        simp [B,eps,Matrix.submatrix,Matrix.fromBlocks]
    rw [←heq,Matrix.det_submatrix_equiv_self]
    simpa only [B,endpoint,zero_mul,zero_add,one_pow,mul_one] using fixedBorder m hm 1 0 t
  have hBdet : B.det=u*hankel m t+(-1)^m*w^2*endpoint m t := by
    rw [hB]
    exact fixedBorder m hpos w u t
  have hpEven : (-1 : ℤ)^p=1 := by rw [hpdouble,pow_mul]; norm_num
  have hsignR : (-1 : ℤ)^r=(-1)^(n+1) := by
    have he : n+1=p+r+2 := by dsimp [r]; omega
    rw [he,pow_add,pow_add,hpEven]; norm_num
  have hsignRM : (-1 : ℤ)^r*(-1)^m=1 := by rw [← pow_add,show r+m=p by omega,hpEven]
  have ha : 2*n-2^(k+1)-1=2*r+1 := by
    have hp2 : 2^(k+1)=2*p := by dsimp [p]; rw [pow_succ]; omega
    rw [hp2]
    dsimp [r]; omega
  have hm : 2^(k+1)-n+1=m := by
    have hp2 : 2^(k+1)=2*p := by dsimp [p]; rw [pow_succ]; omega
    rw [hp2]
  have hH : hankel n t=(-1)^(n+1)*u^(2*r+1)*hankel m t+
      w^2*u^(2*r)*endpoint m t := by
    rw [hHcore,hBdet,show u^(2*r+1)=u^(2*r)*u by rw [pow_succ]]
    have hmain : (-1 : ℤ)^r*u^(2*r)*u*hankel m t=
        (-1)^(n+1)*(u^(2*r)*u)*hankel m t := by rw [hsignR]; ring
    calc
      (-1)^r*u^(2*r)*(u*hankel m t+(-1)^m*w^2*endpoint m t)=
        (-1)^r*u^(2*r)*u*hankel m t+
          ((-1)^r*(-1)^m)*w^2*u^(2*r)*endpoint m t := by ring
      _ = _ := by rw [hmain,hsignRM,one_mul]
  have hv : v=Matrix.of (fun i (_:Unit)=>Fin.lastCases 0 (fun _=>(1:ℤ)) i) := by
    ext i j
    refine Fin.lastCases ?_ (fun i=>?_) i <;> simp [v]
  have hCdet : (fromBlocks B v v.transpose 0).det =
      u*(fromBlocks (Matrix.of fun i j : Fin m=>digitSum (i+j) t)
        (Matrix.of fun (_:Fin m) (_:Unit)=>(1:ℤ))
        (Matrix.of fun (_:Unit) (_:Fin m)=>(1:ℤ)) (0:Matrix Unit Unit ℤ)).det := by
    rw [hB,hv]
    exact concreteCore m (Matrix.of fun i j : Fin m=>digitSum (i+j) t) w u
  have hdetE : (-1)^n*endpoint n t=
      (-1)^r*u^(2*r)*(u*((-1)^m*endpoint m t)) := by
    have hsN := sumBorder n (by omega) t
    have hsM := sumBorder m hpos t
    change (fromBlocks A o o.transpose 0).det=(-1)^n*endpoint n t at hsN
    change _=(-1)^m*endpoint m t at hsM; rw [←hsN,hEcore,hCdet,hsM]
  have hE : endpoint n t=(-1)^n*u^(2*r+1)*endpoint m t := by
    have hsignN : (-1 : ℤ)^n*(-1)^n=1 := by
      rw [←mul_pow]
      simp
    have he : (-1 : ℤ)^n*endpoint n t=u^(2*r+1)*endpoint m t := by
      calc
        (-1)^n*endpoint n t=
            ((-1)^r*(-1)^m)*(u^(2*r)*u)*endpoint m t := by rw [hdetE]; ring
        _=u^(2*r+1)*endpoint m t := by rw [hsignRM,one_mul,pow_succ]
    calc
      endpoint n t=(-1)^n*((-1)^n*endpoint n t) := by rw [←mul_assoc,hsignN,one_mul]
      _=(-1)^n*u^(2*r+1)*endpoint m t := by rw [he]; ring
  dsimp only
  change (hankel n t=(-1)^(n+1)*u^(2*n-2^(k+1)-1)*hankel (2^(k+1)-n+1) t+
    w^2*u^(2*n-2^(k+1)-1-1)*endpoint (2^(k+1)-n+1) t) ∧
    (endpoint n t=(-1)^n*u^(2*n-2^(k+1)-1)*endpoint (2^(k+1)-n+1) t)
  rw [ha,hm,show 2*r+1-1=2*r by omega]
  exact ⟨hH,hE⟩
end D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelRecurrence
