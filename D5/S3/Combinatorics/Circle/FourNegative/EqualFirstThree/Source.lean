/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Source
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-source-table)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual paired physical ladders for all independent equal-first-three gaps. -/
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

/-! No primitive-period or coprimality restriction is imposed on the physical labels. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private chains last_double from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

private def seed (R : ℤ) : ℤ := 1 + R + R * R + R * R * R
private def eta (R : ℤ) : ℤ := R * R + R + 1
private def vcoef (R D : ℤ) : ℤ := D * R * R + D * R + D + 1
private def wcoef (R D : ℤ) : ℤ := D * R * R + (D + 1) * R + 1
private def xcoef (R D : ℤ) : ℤ := (D + 1) * R * R + R + 1

private structure Table (s d : ℕ) (R D N : ℤ) (f g : ℕ → ℤ) : Prop where
  u : ∀ i < d - 1, f i = (2 : ℤ) ^ i * seed R
  un : ∀ i < d - 1, g i = (2 : ℤ) ^ i * (2 * seed R)
  v : ∀ i < s - 1, f (d + i) = (2 : ℤ) ^ i * vcoef R D
  vn : ∀ i < s - 1, g (d + i) = (2 : ℤ) ^ i * (2 * vcoef R D - 1)
  w : ∀ i < s - 1, f (d + s + i) = (2 : ℤ) ^ i * wcoef R D
  wn : ∀ i < s - 1, g (d + s + i) = (2 : ℤ) ^ i * (2 * wcoef R D - R - 1)
  x : ∀ i < s - 1, f (d + s + s + i) = (2 : ℤ) ^ i * xcoef R D
  xn : ∀ i < s - 1, g (d + s + s + i) = (2 : ℤ) ^ i * (2 * xcoef R D - eta R)
  nu : 2 * f (d - 1) = vcoef R D - N
  nun : 2 * g (d - 1) = 2 * vcoef R D - 1 - (2 * N + 1)
  nv : 2 * f (d + s - 1) = wcoef R D - N
  nvn : 2 * g (d + s - 1) = 2 * wcoef R D - R - 1 - (2 * N + 1)
  nw : 2 * f (d + s + s - 1) = xcoef R D - N
  nwn : 2 * g (d + s + s - 1) = 2 * xcoef R D - eta R - (2 * N + 1)
  nx : 2 * f (d + s + s + s - 1) = seed R - N
  nxn : 2 * g (d + s + s + s - 1) = seed R - (2 * N + 1)

set_option maxHeartbeats 1200000 in
private theorem paired_table (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d) :
    let k := 3 * s + d
    let A : ℤ := 1 + 2 ^ s + 2 ^ (2 * s) + 2 ^ (3 * s)
    Table s d (2 ^ s) (2 ^ d) (modulus k)
      (fun i => centered (modulus k) ((2 : ℤ) ^ i * A))
      (fun i => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * A))) := by
  dsimp only
  let R : ℤ := 2 ^ s
  let D : ℤ := 2 ^ d
  let k := 3 * s + d
  let N := modulus k
  let M := modulus (k + 1)
  let A := seed R
  let V := vcoef R D
  let W := wcoef R D
  let X := xcoef R D
  let Vn := 2 * V - 1
  let Wn := 2 * W - R - 1
  let Xn := 2 * X - eta R
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * A)
  let F := fun i : ℕ => centered M ((2 : ℤ) ^ i * A)
  let g := fun i : ℕ => centered M ((2 : ℤ) ^ i * (2 * A))
  have hA : (1 + (2 : ℤ) ^ s + 2 ^ (2 * s) + 2 ^ (3 * s)) = A := by
    dsimp [A, seed, R]
    rw [show 2 * s = s + s by omega, show 3 * s = s + s + s by omega]
    simp only [pow_add]
  rw [hA]
  change Table s d R D N f g
  have hN : N = D * R * R * R - 1 := by
    dsimp [N, k, modulus, D, R]
    rw [show 3 * s + d = d + s + s + s by omega]
    simp only [pow_add] <;> ring
  have hM : M = 2 * N + 1 := by dsimp [M, N, modulus]; rw [pow_succ]; ring
  have old := chains s s s d hs hs hs hd
  have new := chains s s s (d + 1) hs hs hs (by omega)
  have hk : s + s + s + d = k := by omega
  have hkn : s + s + s + (d + 1) = k + 1 := by omega
  rw [hk] at old
  rw [hkn] at new
  obtain ⟨_, hU, hV, hW, hX⟩ := old
  obtain ⟨_, hUn, hVn, hWn, hXn⟩ := new
  have eoV : 1 + D + D * R + D * R * R = V := by dsimp [V, vcoef]; ring
  have eoW : 1 + R + R * D + R * D * R = W := by dsimp [W, wcoef]; ring
  have eoX : 1 + R + R * R + R * R * D = X := by dsimp [X, xcoef]; ring
  change ∀ i < d, f i = if i + 1 < d then 2 ^ i * A else -(N - (1 + D + D * R + D * R * R))/2 at hU
  change ∀ i < s, f (d + i) = if i + 1 < s then 2 ^ i * (1 + D + D * R + D * R * R) else -(N - (1 + R + R * D + R * D * R))/2 at hV
  change ∀ i < s, f (d + s + i) = if i + 1 < s then 2 ^ i * (1 + R + R * D + R * D * R) else -(N - (1 + R + R * R + R * R * D))/2 at hW
  change ∀ i < s, f (d + s + s + i) = if i + 1 < s then 2 ^ i * (1 + R + R * R + R * R * D) else -(N - A)/2 at hX
  rw [eoV] at hU
  rw [eoV, eoW] at hV
  rw [eoW, eoX] at hW
  rw [eoX] at hX
  have hDn : (2 : ℤ) ^ (d + 1) = 2 * D := by dsimp [D]; rw [pow_succ]; ring
  simp only [hDn] at hUn hVn hWn hXn
  have eV : 1 + 2 * D + 2 * D * R + 2 * D * R * R = Vn := by dsimp [Vn, V, vcoef]; ring
  have eW : 1 + R + R * (2 * D) + R * (2 * D) * R = Wn := by dsimp [Wn, W, wcoef]; ring
  have eX : 1 + R + R * R + R * R * (2 * D) = Xn := by dsimp [Xn, X, xcoef, eta]; ring
  change ∀ i < d + 1, F i = if i + 1 < d + 1 then 2 ^ i * A else -(M - (1 + 2 * D + 2 * D * R + 2 * D * R * R))/2 at hUn
  change ∀ i < s, F (d + 1 + i) = if i + 1 < s then 2 ^ i * (1 + 2 * D + 2 * D * R + 2 * D * R * R) else -(M - (1 + R + R * (2 * D) + R * (2 * D) * R))/2 at hVn
  change ∀ i < s, F (d + 1 + s + i) = if i + 1 < s then 2 ^ i * (1 + R + R * (2 * D) + R * (2 * D) * R) else -(M - (1 + R + R * R + R * R * (2 * D)))/2 at hWn
  change ∀ i < s, F (d + 1 + s + s + i) = if i + 1 < s then 2 ^ i * (1 + R + R * R + R * R * (2 * D)) else -(M - A)/2 at hXn
  rw [eV] at hUn
  rw [eV, eW] at hVn
  rw [eW, eX] at hWn
  rw [eX] at hXn
  have shift (i : ℕ) : g i = F (i + 1) := by dsimp [g, F]; rw [pow_succ]; congr 1; ring
  have rU : (2 : ℤ) ^ d * A = N + V := by change D * A = N + V; rw [hN]; dsimp [A, V, seed, vcoef]; ring
  have rV : (2 : ℤ) ^ s * V = N + W := by change R * V = N + W; rw [hN]; dsimp [V, W, vcoef, wcoef]; ring
  have rW : (2 : ℤ) ^ s * W = N + X := by change R * W = N + X; rw [hN]; dsimp [W, X, wcoef, xcoef]; ring
  have rX : (2 : ℤ) ^ s * X = N + A := by change R * X = N + A; rw [hN]; dsimp [X, A, xcoef, seed]; ring
  have rnU : (2 : ℤ) ^ (d + 1) * A = M + Vn := by rw [hDn, hM]; dsimp [Vn]; linarith only [rU]
  have rnV : (2 : ℤ) ^ s * Vn = M + Wn := by change R * Vn = M + Wn; rw [hM, hN]; dsimp [Vn, V, Wn, W, vcoef, wcoef]; ring
  have rnW : (2 : ℤ) ^ s * Wn = M + Xn := by change R * Wn = M + Xn; rw [hM, hN]; dsimp [Wn, W, Xn, X, wcoef, xcoef, eta]; ring
  have rnX : (2 : ℤ) ^ s * Xn = M + A := by change R * Xn = M + A; rw [hM, hN]; dsimp [Xn, X, A, xcoef, eta, seed]; ring
  constructor
  · intro i hi; exact (hU i (by omega)).trans (if_pos (by omega))
  · intro i hi; rw [shift, hUn (i + 1) (by omega), if_pos (by omega), pow_succ]; dsimp [A]; ring
  · intro i hi; exact (hV i (by omega)).trans (if_pos (by omega))
  · intro i hi; rw [shift, show d + i + 1 = d + 1 + i by omega, hVn i (by omega), if_pos (by omega)]
  · intro i hi; exact (hW i (by omega)).trans (if_pos (by omega))
  · intro i hi; rw [shift, show d + s + i + 1 = d + 1 + s + i by omega, hWn i (by omega), if_pos (by omega)]
  · intro i hi; exact (hX i (by omega)).trans (if_pos (by omega))
  · intro i hi; rw [shift, show d + s + s + i + 1 = d + 1 + s + s + i by omega, hXn i (by omega), if_pos (by omega)]
  · rw [hU (d - 1) (by omega), if_neg (by omega)]
    exact last_double N A V d (by omega) rU
  · rw [shift, show d - 1 + 1 = d by omega, hUn d (by omega), if_neg (by omega), ←hM]
    exact last_double M A Vn (d + 1) (by omega) rnU
  · rw [show d + s - 1 = d + (s - 1) by omega, hV (s - 1) (by omega), if_neg (by omega)]
    exact last_double N V W s (by omega) rV
  · rw [shift, show d + s - 1 + 1 = d + 1 + (s - 1) by omega, hVn (s - 1) (by omega), if_neg (by omega), ←hM]
    exact last_double M Vn Wn s (by omega) rnV
  · rw [show d + s + s - 1 = d + s + (s - 1) by omega, hW (s - 1) (by omega), if_neg (by omega)]
    exact last_double N W X s (by omega) rW
  · rw [shift, show d + s + s - 1 + 1 = d + 1 + s + (s - 1) by omega, hWn (s - 1) (by omega), if_neg (by omega), ←hM]
    exact last_double M Wn Xn s (by omega) rnW
  · rw [show d + s + s + s - 1 = d + s + s + (s - 1) by omega, hX (s - 1) (by omega), if_neg (by omega)]
    exact last_double N X A s (by omega) rX
  · rw [shift, show d + s + s + s - 1 + 1 = d + 1 + s + s + (s - 1) by omega, hXn (s - 1) (by omega), if_neg (by omega), ←hM]
    exact last_double M Xn A s (by omega) rnX

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
