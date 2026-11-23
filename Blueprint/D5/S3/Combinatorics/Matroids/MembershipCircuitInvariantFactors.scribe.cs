using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class MembershipCircuitInvariantFactorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/MembershipCircuitInvariantFactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral lifting obstruction for omitted bases separated by their membership classes.",
        H("Cyclic Factors from Petal Membership"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("membership-lifting-obstruction-invariant-factors"),
                DeclarationHandle.Create(Module + ".membership_lifting_obstruction_invariant_factors"),
                H("Independent replacement for separated petals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the ordered core have K elements and suppose 3 <= r < K."
                    + " Its bases are all r-element sets outside a family of t omissions sharing a pivot."
                    + " Partition the remaining indices by their membership in the petals."
                    + " For each pair of petals, require a membership class of at least two indices lying in exactly one of the two petals."
                    + " In a finite block-ordered parallel expansion, let n be the total size, g the gcd of all class sizes, and q(T) the gcd of n and the class sizes outside T."
                    + " Both binom(K - 2, r - 2) and binom(K - 2, r - 1) are at least t."
                    + " The integral joint lifting obstruction is the direct sum of binom(K - 2, r - 2) - t cyclic factors of order g, binom(K - 2, r - 1) - t of order n, and one factor of order q(T) per omission."
                    + " Weight concentration within each membership class separates the omitted coefficients."
                    + " Deletion and complement injections give the multiplicity bounds."))),
                DescribeRole.Theorem))));
}
