using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SumProductGoldenMinimizerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/SumProductGoldenMinimizerRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A seven-point positive-real set with at most seventeen products can have at most "
            + "twenty-two sums, while the corresponding golden set has at least twenty-four.",
        H("O'Bryant's Golden Minimizer Question Is Refuted"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-set"),
                DeclarationHandle.Create(Prefix + "goldenSet"),
                H("Golden power set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural number n, goldenSet n is the image of the integers from "
                        + "one through n under the powers of the real golden ratio."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-minimizer-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Golden minimizer claim"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every n at least three, every positive n-element finite set A "
                        + "whose product set has cardinality at most 3n minus 4 has a "
                        + "sum set at least as large as the sum set of goldenSet n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-minimizer-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A plastic-root counterexample"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real root r in the interval (1,2) of r cubed minus r minus "
                            + "one equals zero yields A equal to the seven powers with "
                            + "exponents 0, 3, 5, 6, 7, 8 and 9. Products lie in the image "
                            + "of the sixteen-element exponent sumset, so their cardinality "
                            + "is at most seventeen.")),
                    Paragraph(Text(
                        "The identities obtained from r cubed equal r plus one are encoded "
                            + "by coefficient vectors in the integers cubed. Their pointwise "
                            + "sumset has twenty-two vectors, and evaluation at r covers A+A. "
                            + "The existing geometric seven-term bound gives at least twenty-four "
                            + "sums for the golden set at n equal to seven. These inequalities "
                            + "contradict the claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("obryant-2024-golden-minimizer-refutation"),
                    ResolutionKind.Refuted))),
        []));
}
