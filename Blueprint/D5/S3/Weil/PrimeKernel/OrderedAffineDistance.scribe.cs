using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeKernel;

internal sealed class OrderedAffineDistanceDocument : IScribeDocumentDefinition
{
    private const string Criterion =
        "D5/S3/Weil/PrimeKernel/OrderedAffineDistance."
            + "posdef_iff_threshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal ordered affine distance kernel has an exact complex cut-energy "
            + "decomposition and a sharp finite positive-definiteness threshold.",
        H("Ordered Affine Distance Energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-affine-distance-energy-threshold"),
                DeclarationHandle.Create(Criterion),
                H("The literal distance kernel is positive definite exactly above the endpoint threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a monotone finite ordered family of real nodes, the matrix entry is "
                            + "literally L-|t_i-t_j|. The proof expands each ordered distance into "
                            + "the intervening gaps and rewrites every crossing cut through the "
                            + "complex prefix and suffix norm squares.")),
                    Paragraph(Text(
                        "The resulting identity is valid for arbitrary complex coefficients, "
                            + "including the one-node case. In centered form it is (L-D/2)|M|² "
                            + "plus twice the positive gap-weighted sum of |C_k-M/2|². Strictly "
                            + "increasing nodes make every gap positive; a zero-total nonzero "
                            + "coefficient vector has a nonzero proper prefix.")),
                    Paragraph(Text(
                        "The endpoint two-coordinate restriction gives the converse threshold. "
                            + "This finite theorem concerns the literal distance matrix only. It "
                            + "does not prove the analytic actual-prime-kernel mixture bound "
                            + "K>=rA or global Riemann-hypothesis implications."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The ordered cut decomposition and the centered complex energy are the new "
                    + "content consumed by the sharp criterion; generic positive-matrix "
                    + "hypotheses are not used as a substitute."))
        )));
}
