/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Strict
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Strict
   mirror-E: none(waiver:consumed-strict-upper-schedule)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: The explicit high-X split and literal third-packet ear for every a greater than s. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
/-! Physical interval and prefix bounds for the stated family. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude delta heads newHeads successor newSuccessor start length f g N source source_numeric
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Source
open private Checks strict_checks
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Arithmetic
open private block_data terminal_signs checks_strip range_end range_join finish
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private theorem inventory (a s : ℕ) (hs : 2 ≤ s) (ha : s < a) :
    (List.range' (a + 2 * s - 1) (s + 1) ++ List.range (3 * s - 1) ++
      List.range' (3 * s) (a - s - 1) ++ [3 * s - 1]).Perm (List.range (rank a s)) := by
  let b := 3 * s - 1
  let c := a + 2 * s - 1
  let k := rank a s
  have h1 : List.range b ++ [b]=List.range (b + 1) := List.range_succ.symm
  have h2 : List.range (b + 1) ++ List.range' (3 * s) (a - s - 1) = List.range c := by
    simpa only [List.range_eq_range', Nat.zero_add, 
      show b + 1 = 3 * s by dsimp [b];omega, 
      show 3 * s + (a - s - 1) = c by dsimp [c];omega] using
      range_join 0 (b + 1) (a - s - 1)
  have h3 : List.range c ++ List.range' c (s + 1) = List.range k := by
    simpa only [List.range_eq_range', Nat.zero_add, 
      show c + (s + 1) = k by dsimp [c, k, rank];omega] using range_join 0 c (s + 1)
  have hh : (List.range b ++ [b]) ++ List.range' (3 * s) (a - s - 1) ++
      List.range' c (s + 1) = List.range k := by rw [h1, h2, h3]
  apply List.Perm.trans (l₂ := (List.range b ++ [b]) ++
      List.range' (3 * s) (a - s - 1) ++ List.range' c (s + 1))
  · apply Multiset.coe_eq_coe.mp
    dsimp [b, c]
    simp only [←Multiset.coe_add]
    ac_rfl
  · exact List.Perm.of_eq hh

set_option maxHeartbeats 2400000 in
private theorem strict (a s : ℕ) (hs : 2 ≤ s) (ha : s < a) :
    ∃ sigma : List (Fin (rank a s)), 
      sigma.map Fin.val =
        List.range' (a + 2 * s - 1) (s + 1) ++ List.range (3 * s - 1) ++
          List.range' (3 * s) (a - s - 1) ++ [3 * s - 1] ∧
      3 * s ≤ rank a s ∧ OriginalOrder (rank a s) (amplitude a s) sigma ∧
      OriginalOrder (rank a s + 1) (2 * amplitude a s) (earWord (rank a s) sigma (3 * s)) := by
  let q : ℤ := 2 ^ s
  let h : ℤ := 2 ^ (a - s)
  let e : ℤ := 2 ^ (a - s - 1)
  let r : ℤ := 2 ^ (s - 1)
  let A := heads (h * q) q 0
  let B := heads (h * q) q 1
  let L := heads (h * q) q 2
  let M := heads (h * q) q 3
  let Bn := newHeads (h * q) q 1
  let Ln := newHeads (h * q) q 2
  let Mn := newHeads (h * q) q 3
  have hx : (2:ℤ) ^ a = h * q := by
    dsimp [h, q]; rw [←pow_add]; congr 1;omega
  have hq : 4 ≤ q := by
    simpa [q] using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hs
  have hh : 2 ≤ h := by
    simpa [h] using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show 1 ≤ a - s by omega)
  have he : 2 * e = h := by
    dsimp [e, h]
    conv_rhs => rw [show a - s = a - s - 1 + 1 by omega, pow_succ]
    ring
  have hr : 2 * r = q := by
    dsimp [r, q]
    conv_rhs => rw [show s = s - 1 + 1 by omega, pow_succ]
    ring
  let P := List.range' (a + 2 * s - 1) s
  let U := List.range (s - 1)
  let V := List.range' s (s - 1)
  let W := List.range' (2 * s) (s - 1)
  let X := List.range' (3 * s) (a - s - 1)
  let nx := 3 * s + a - 1
  let nu := s - 1
  let nv := 2 * s - 1
  let nw := 3 * s - 1
  let bs := [(P, nx), (U, nu), (V, nv), (W++X, nw)]
  let bsn := [(P, nx), (U, nu), (V++[rank a s], nv), (W++X, nw)]
  have bP := block_data a s hs ha.le 3 (a - s - 1) s (by simp [length];omega)
  rw [show start s 3 + (a - s - 1) = a + 2 * s - 1 by dsimp [start];omega, hx] at bP
  change (P.map (f a s)).sum = (q - 1) * e * M ∧
    (P.map (g a s)).sum = (q - 1) * e * Mn ∧
    (∀ i ∈ P, 0 ≤ f a s i) ∧ (∀ i ∈ P, 0 ≤ g a s i) at bP
  have bU := block_data a s hs ha.le 0 0 (s - 1) (by simp [length])
  rw [hx] at bU
  simp only [start, Matrix.cons_val_zero, Nat.zero_add, ←List.range_eq_range'] at bU
  change (U.map (f a s)).sum = (r - 1) * 1 * A ∧
    (U.map (g a s)).sum = (r - 1) * 1 * (2 * A) ∧
    (∀ i ∈ U, 0 ≤ f a s i) ∧ (∀ i ∈ U, 0 ≤ g a s i) at bU
  have bV := block_data a s hs ha.le 1 0 (s - 1) (by simp [length])
  rw [hx] at bV
  change (V.map (f a s)).sum = (r - 1) * 1 * B ∧
    (V.map (g a s)).sum = (r - 1) * 1 * Bn ∧
    (∀ i ∈ V, 0 ≤ f a s i) ∧ (∀ i ∈ V, 0 ≤ g a s i) at bV
  have bW := block_data a s hs ha.le 2 0 (s - 1) (by simp [length])
  rw [hx] at bW
  change (W.map (f a s)).sum = (r - 1) * 1 * L ∧
    (W.map (g a s)).sum = (r - 1) * 1 * Ln ∧
    (∀ i ∈ W, 0 ≤ f a s i) ∧ (∀ i ∈ W, 0 ≤ g a s i) at bW
  have bX := block_data a s hs ha.le 3 0 (a - s - 1) (by simp [length];omega)
  rw [hx] at bX
  change (X.map (f a s)).sum = (e - 1) * 1 * M ∧
    (X.map (g a s)).sum = (e - 1) * 1 * Mn ∧
    (∀ i ∈ X, 0 ≤ f a s i) ∧ (∀ i ∈ X, 0 ≤ g a s i) at bX
  have tab := source a s hs ha.le
  rw [hx] at tab
  have ear : g a s (rank a s) = A := tab.2.2.2.2
  have nP := tab.2.2.2.1 3
  have nU := tab.2.2.2.1 0
  have nV := tab.2.2.2.1 1
  have nW := tab.2.2.2.1 2
  have ix : start s 3 + length a s 3 - 1 = nx := by dsimp[start, length, nx] <;> omega
  have iu : start s 0 + length a s 0 - 1 = nu := by dsimp[start, length, nu];omega
  have iv : start s 1 + length a s 1 - 1 = nv := by dsimp[start, length, nv];omega
  have iw : start s 2 + length a s 2 - 1 = nw := by dsimp[start, length, nw];omega
  rw [ix] at nP
  rw [iu] at nU
  rw [iv] at nV
  rw [iw] at nW
  change 2 * f a s nx = A - N a s ∧ 2 * g a s nx = A - (2 * N a s + 1) at nP
  change 2 * f a s nu = B - N a s ∧ 2 * g a s nu = Bn - (2 * N a s + 1) at nU
  change 2 * f a s nv = L - N a s ∧ 2 * g a s nv = Ln - (2 * N a s + 1) at nV
  change 2 * f a s nw = M - N a s ∧ 2 * g a s nw = Mn - (2 * N a s + 1) at nW
  have hN : N a s = h * q ^ 4 - 1 := by rw [(source_numeric a s).1, hx] <;> dsimp [q] <;> ring
  have hhalf : 2 * (N a s/2) = N a s - 1 := by
    have heq : N a s = 2 * (h * r * q ^ 3 - 1) + 1 := by rw [hN];linear_combination -h * q ^ 3 * hr
    omega
  have hcap : 0 ≤ N a s/2 := by
    have hpow : 4 ≤ (2:ℤ) ^ rank a s := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show 2 ≤ rank a s by dsimp[rank];omega)
    rw [←(source_numeric a s).2.1]
    dsimp [modulus];omega
  have cert := strict_checks h q hh hq
  change Checks _ _ _ ∧ Checks _ _ _ at cert
  rw [←hN] at cert
  have fp : 2 * (P.map (f a s)).sum = h * (q - 1) * M := by rw [bP.1];linear_combination (q - 1) * M * he
  have gp : 2 * (P.map (g a s)).sum = h * (q - 1) * Mn := by rw [bP.2.1];linear_combination (q - 1) * Mn * he
  have fu : 2 * (U.map (f a s)).sum = (q - 2) * A := by rw [bU.1];linear_combination A * hr
  have gu : 2 * (U.map (g a s)).sum = (q - 2) * (2 * A) := by rw [bU.2.1];linear_combination (2 * A) * hr
  have fv : 2 * (V.map (f a s)).sum = (q - 2) * B := by rw [bV.1];linear_combination B * hr
  have gv : 2 * ((V++[rank a s]).map (g a s)).sum = (q - 2) * Bn + 2 * A := by
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ear, bV.2.1]
    linear_combination Bn * hr
  have fw : 2 * ((W++X).map (f a s)).sum = (q - 2) * L + (h - 2) * M := by
    rw [List.map_append, List.sum_append, bW.1, bX.1];linear_combination L * hr + M * he
  have gw : 2 * ((W++X).map (g a s)).sum = (q - 2) * Ln + (h - 2) * Mn := by
    rw [List.map_append, List.sum_append, bW.2.1, bX.2.1];linear_combination Ln * hr + Mn * he
  have nsP := terminal_signs a s hs ha.le 3
  have nsU := terminal_signs a s hs ha.le 0
  have nsV := terminal_signs a s hs ha.le 1
  have nsW := terminal_signs a s hs ha.le 2
  rw [ix] at nsP
  rw [iu] at nsU
  rw [iv] at nsV
  rw [iw] at nsW
  have hold : InStrip (f a s) (N a s/2) 0 (blocksWord bs) := by
    apply checks_strip _ _ _ hcap
    · intro b hb i hi
      simp only [bs, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · exact bP.2.2.1 i hi
      · exact bU.2.2.1 i hi
      · exact bV.2.2.1 i hi
      · rcases List.mem_append.mp hi with hi|hi
        · exact bW.2.2.1 i hi
        · exact bX.2.2.1 i hi
    · intro b hb
      simp only [bs, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · exact nsP.1
      · exact nsU.1
      · exact nsV.1
      · exact nsW.1
    · simpa only [bs, List.map_cons, List.map_nil, hhalf, fp, fu, fv, fw, nP.1, nU.1, nV.1, nW.1] using cert.1
  have hnew : InStrip (g a s) (N a s) 0 (blocksWord bsn) := by
    apply checks_strip _ _ _ (by omega)
    · intro b hb i hi
      simp only [bsn, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · exact bP.2.2.2 i hi
      · exact bU.2.2.2 i hi
      · rcases List.mem_append.mp hi with hi|hi
        · exact bV.2.2.2 i hi
        · have heq := List.mem_singleton.mp hi;subst i;rw [ear];exact (tab.1 0).le
      · rcases List.mem_append.mp hi with hi|hi
        · exact bW.2.2.2 i hi
        · exact bX.2.2.2 i hi
    · intro b hb
      simp only [bsn, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · exact nsP.2
      · exact nsU.2
      · exact nsV.2
      · exact nsW.2
    · simpa only [bsn, List.map_cons, List.map_nil, gp, gu, gv, gw, nP.2, nU.2, nV.2, nW.2] using cert.2
  have hP : P++[nx]=List.range' (a + 2 * s - 1) (s + 1) := by
    simpa only [P, show a + 2 * s - 1 + s = nx by dsimp[nx];omega] using range_end (a + 2 * s - 1) s
  have hU : U++[nu]=List.range s := by
    simpa only [U, nu, Nat.succ_eq_add_one, show s - 1 + 1 = s by omega] using (List.range_succ (n:=s - 1)).symm
  have hV : V++[nv]=List.range' s s := by
    simpa only [V, show s + (s - 1) = nv by dsimp[nv];omega, show s - 1 + 1 = s by omega] using range_end s (s - 1)
  have hUV : (U++[nu])++(V++[nv]) = List.range (2 * s) := by
    rw [hU, hV]
    simpa only [List.range_eq_range', Nat.zero_add, show s + s = 2 * s by omega] using range_join 0 s s
  have hUVW : ((U++[nu])++(V++[nv]))++W = List.range (3 * s - 1) := by
    rw [hUV]
    simpa only [W, List.range_eq_range', Nat.zero_add, show 2 * s + (s - 1) = 3 * s - 1 by omega] using range_join 0 (2 * s) (s - 1)
  let pre := P++[nx]++U++[nu]++V
  let post := nv::(W++X)++[nw]
  have hw : pre++post = List.range' (a + 2 * s - 1) (s + 1)++List.range (3 * s - 1)++X++[nw] := by
    calc
      pre++post = (P++[nx])++(((U++[nu])++(V++[nv]))++W)++X++[nw] := by
        simp only [pre, post, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
      _ = _ := by rw [hP, hUVW]
  have hp : (pre++post).Perm (List.range (rank a s)) := by
    rw [hw];exact inventory a s hs ha
  have hc : pre.length = 3 * s := by simp [pre, P, U, V];omega
  have ho : blocksWord bs = pre++post := by
    simp [blocksWord, bs, pre, post, List.append_assoc]
  have hn : blocksWord bsn = pre++rank a s::post := by
    simp [blocksWord, bsn, pre, post, List.append_assoc]
  rw [ho] at hold
  rw [hn] at hnew
  obtain ⟨sigma, hvals, hcut, hold, hnew⟩ := finish a s hs ha.le (3 * s) pre post hc hp hold hnew
  refine ⟨sigma, ?_, hcut, hold, hnew⟩
  rw [hvals, hw]
end D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
