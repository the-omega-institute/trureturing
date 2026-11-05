// Scribe: D5/S3/Combinatorics/Circle/MersenneWeight
// This is a faithful application record for the source-preparation artifact.
// It records assumptions, mechanism, scope, and open boundaries; it is not a
// kernel receipt and it does not turn uncompiled Lean text into an admission.

namespace D5.S3.Combinatorics.Circle.MersenneWeight;

public sealed class RigidityApplication
{
    public const string Statement =
        "For r >= 2 and nonempty es : List Nat, if (2^r - 1) divides " +
        "sum(es.map (e => 2^e)), the coefficient pushforward is fed to the " +
        "nonempty cyclic binary normal form; consequently r <= es.length, " +
        "and es.length = r exactly when es.map(e => e % r) is Perm (range r).";

    public const string Assumptions =
        "Only standard Nat/List/Finset arithmetic and the public " +
        "ZeroSumSubsets.cyclic_binary_normal_form are used. Its first four " +
        "fields supply A.Nonempty, the integer carry equation, coefficient " +
        "weight, and coefficient-sum length. No carry induction is recreated.";

    public const string Mechanism =
        "Push es to n(i) = count of e % r equal to i. Recursive lemmas prove " +
        "sum_i n(i) = es.length and sum_i n(i) * 2^i = sum_e 2^(e % r). " +
        "Nat.ModEq transports every 2^e to 2^(e % r) using 2^r congruent " +
        "to 1 modulo 2^r-1. The normal form then makes the endpoint mask " +
        "a positive divisor of the Mersenne modulus. Geometric-sum bounds and " +
        "Finset.geomSum_injective force A = univ; the length is r + sum m. " +
        "Equality forces every carry to vanish and every residue count to be " +
        "one, which is exactly the List.Perm characterization.";

    public const string FourBitScribe =
        "For a,b,c >= 2 and X = 1 + 2^a + 2^(a+b) + 2^(a+b+c), any " +
        "Mersenne divisor 2^r-1 has r <= 4 by the general theorem. Exact " +
        "tests are: 3 | X iff the parity residue counts are (2,2); 7 | X " +
        "iff the mod-3 counts are (3,0,1) or (1,3,0); and 15 | X iff the " +
        "four mod-4 residues occur once. Combined with the supplied narrow " +
        "orbit theorem, the conditional abstract interval candidates are " +
        "{2X/3, 4X/7, 6X/7, 8X/15, 14X/15}, subject to the displayed " +
        "denominator dividing X.";

    public const string Limits =
        "The narrow orbit theorem is independently owned and is not imported " +
        "or assumed as a kernel theorem here. Physical common permutations and " +
        "the full J classification remain open. The four-bit tests and the " +
        "odd-X binary-weight-at-most-four specialization are applications of " +
        "the arithmetic theorem and remain transient at this layer. This file " +
        "has no compiler, Kernel, Reg, or official acceptance claim.";

    public const string Provenance =
        "Normal-form source: D5/S3/Combinatorics/Circle/ZeroSumSubsets.lean, " +
        "repository source SHA 69676cedb1cc867d36647608c976bb1281520e58994cd6ad45de88117877ffec. " +
        "Stable ordinary inputs are cited only as fallible application context: " +
        "four-bit answer SHA 581fd10fe192b9127213eb492f1fefdbbc8f0d7c3c1db0a85d3831838ca8c2f2; " +
        "terminal conclusion SHA fac88f2b76331b4caa39ba795118cf394362c39a645954eb4c0afa6e20877925.";
}

}
