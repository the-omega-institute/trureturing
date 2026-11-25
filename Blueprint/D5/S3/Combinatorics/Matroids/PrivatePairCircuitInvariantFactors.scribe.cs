using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PrivatePairCircuitInvariantFactorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PrivatePairCircuitInvariantFactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral lifting obstruction when each omitted basis has a private pair.",
        H("Cyclic Factors for Overlapping Omissions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("private-pair-lifting-obstruction-invariant-factors"),
                DeclarationHandle.Create(Module + ".private_pair_lifting_obstruction_invariant_factors"),
                H("Independent cyclic-factor replacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use an ordered ambient set of K elements and let 3 <= r < K."
                    + " Its core bases are exactly the r-element subsets outside a family of t omitted r-element subsets."
                    + " All omissions contain a fixed element, and each contains two distinct elements belonging to no other omission."
                    + " Use a finite block-ordered parallel expansion with a nonempty class above each ground element."
                    + " Let n be the total size, g the greatest common divisor of the class sizes, and q(T) the greatest common divisor of n and the class sizes outside T."
                    + " Put A = binom(K - 2, r - 2) and B = binom(K - 2, r - 1)."
                    + " Private pairs force A and B to be at least t."
                    + " Let L be the image of the integral simultaneous circuit restriction on the expanded matroid."
                    + " Its target is the product of the integral top-cycle lattices of the contractions by all circuits."
                    + " Each component sums the signed restrictions obtained by deleting each vertex of that circuit in turn."
                    + " The integer module of target tuples with a nonzero multiple in L, modulo L, is the direct sum of A - t cyclic factors of order g, B - t of order n, and one factor of order q(T) per omission."
                    + " The residue product identity permits induction by finite integral-module cancellation."))),
                DescribeRole.Theorem))));
}
