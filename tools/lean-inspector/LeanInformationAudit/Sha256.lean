namespace LeanInformationAudit.Sha256

private def initial : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def rotateRight (word : UInt32) (count : Nat) : UInt32 :=
  (word >>> UInt32.ofNat count) ||| (word <<< UInt32.ofNat (32 - count))

private def choose (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (~~~x &&& z)

private def majority (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def bigSigma0 (word : UInt32) : UInt32 :=
  rotateRight word 2 ^^^ rotateRight word 13 ^^^ rotateRight word 22

private def bigSigma1 (word : UInt32) : UInt32 :=
  rotateRight word 6 ^^^ rotateRight word 11 ^^^ rotateRight word 25

private def smallSigma0 (word : UInt32) : UInt32 :=
  rotateRight word 7 ^^^ rotateRight word 18 ^^^ (word >>> 3)

private def smallSigma1 (word : UInt32) : UInt32 :=
  rotateRight word 17 ^^^ rotateRight word 19 ^^^ (word >>> 10)

private def padded (input : ByteArray) : ByteArray := Id.run do
  let mut result := input.push 0x80
  while result.size % 64 != 56 do
    result := result.push 0
  let bitLength := UInt64.ofNat input.size * 8
  for shift in [0:8] do
    let amount := UInt64.ofNat ((7 - shift) * 8)
    result := result.push ((bitLength >>> amount).toUInt8)
  pure result

private def readWord (input : ByteArray) (offset : Nat) : UInt32 :=
  (input[offset]!.toUInt32 <<< 24) |||
  (input[offset + 1]!.toUInt32 <<< 16) |||
  (input[offset + 2]!.toUInt32 <<< 8) |||
  input[offset + 3]!.toUInt32

private def schedule (input : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut words := Array.replicate 64 0
  for index in [0:16] do
    words := words.set! index (readWord input (offset + index * 4))
  for index in [16:64] do
    let word := smallSigma1 words[index - 2]! + words[index - 7]! +
      smallSigma0 words[index - 15]! + words[index - 16]!
    words := words.set! index word
  pure words

private def compress (state words : Array UInt32) : Array UInt32 := Id.run do
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for index in [0:64] do
    let first := h + bigSigma1 e + choose e f g + roundConstants[index]! + words[index]!
    let second := bigSigma0 a + majority a b c
    h := g
    g := f
    f := e
    e := d + first
    d := c
    c := b
    b := a
    a := first + second
  pure #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
    state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- Compute the SHA-256 digest bytes of an arbitrary byte array. -/
def digest (input : ByteArray) : ByteArray := Id.run do
  let input := padded input
  let mut state := initial
  for block in [:input.size / 64] do
    state := compress state (schedule input (block * 64))
  let mut result := ByteArray.empty
  for word in state do
    result := result.push (word >>> 24).toUInt8
    result := result.push (word >>> 16).toUInt8
    result := result.push (word >>> 8).toUInt8
    result := result.push word.toUInt8
  pure result

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat ('0'.toNat + value)
  else Char.ofNat ('a'.toNat + value - 10)

/-- Compute a 64-character lowercase hexadecimal SHA-256 digest. -/
def hex (input : ByteArray) : String :=
  String.ofList <| (digest input).toList.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

end LeanInformationAudit.Sha256
