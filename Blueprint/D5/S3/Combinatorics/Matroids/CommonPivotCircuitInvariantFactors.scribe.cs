using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CommonPivotCircuitInvariantFactorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CommonPivotCircuitInvariantFactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral joint lifting obstruction for common-pivot sparse-paving omissions.",
        H("Cyclic Factors at a Common Pivot"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-pivot-lifting-obstruction-invariant-factors"),
                DeclarationHandle.Create(Module + ".common_pivot_lifting_obstruction_invariant_factors"),
                H("Cyclic factors with only the intersection bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let 3 <= r < K for a finite ordered ground set of size K."
                    + " The core bases are all r-element subsets except t omitted sets."
                    + " All omissions contain a common element, and distinct omissions intersect in at most r minus two elements."
                    + " In a finite block-ordered parallel expansion write n for the total size, g for the gcd of the class sizes, and q(T) for the gcd of n and the class sizes outside T."
                    + " The lifting obstruction is integrally linearly equivalent to the product of binom(K minus 2, r minus 2) minus t factors of order g, binom(K minus 2, r minus 1) minus t factors of order n, and one factor of order q(T) per omission."
                    + " The two binomial coefficients are at least t."
                    + " The primary exchange and the existing finite cancellation argument prove the decomposition."))),
                DescribeRole.Theorem))));
}
