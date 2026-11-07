using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class WuA227244ConjectureThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/WuA227244ConjectureThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/wu2026a227244c3");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under two independent progression noncoverage hypotheses, 149 is the least prime divisor for every natural index.",
        H("A conditional progression interpretation of Wu's third conjecture for A227244"),
        Blocks(
            Paragraph(Text("All indices and exponents are natural numbers. The outer arithmetic, including the final subtraction, is in the integers. The symbol G denotes the signed integer itself, without a natural subtraction or absolute value.")),
            Node("G", "The nested exponential integer",
                "OEIS A227244, NAME: Smallest prime factor of (2^(2^n) + 1)*2^(2^(2^n)) - 1. The exponent of the second outer power is two raised to two raised to m.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reduced", "Finite residues of the nested powers",
                "This residue expression is in ZMod q. Its five natural parameters are q, d, p, L and r; L records the period used to choose r. The first exponent is reduced modulo d. For the second exponent, a tail of length p precedes reduction modulo p, and the resulting outer exponent is reduced modulo d. Periodicity of powers along 72*n+32 transfers this expression to every natural n.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The exact conditional least-prime assertion",
                "The source says: Conjecture 3: a(72*n+32) = 149 for n >= 0 and a(72*n+32) is not covered by Conjectures 1 and 2. We use the disclosed progression-index CONDITIONAL interpretation: for each natural n, absence of a natural k with 72*n+32=20*k+16 and, independently, absence of a natural k with 72*n+32=220*k+8 imply the least-prime conclusion. This quantified formula is our interpretation, not an author-written formula or established author intent. Both k binders range independently over all natural numbers, including zero; n also includes zero and is unbounded. The first hypothesis gives n mod 5 different from 2 and excludes the prime 101; the second gives n mod 55 different from 18 and excludes 47. Periodic modular transfer proves divisibility by 149 and excludes all 34 smaller primes. No extra exclusion, finite prefix or eventual onset is assumed. The proof composes existing periodicity, casts and finite calculations; it claims no new general method", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("wu-a227244-conjecture-three"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a227244c3-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

}
