using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BinaryUnitaryOptimizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BinaryUnitaryOptimization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, "Scalar phases attain the two-column complex norm bound.",
            "evidence-not-specified-by-formal-manifest"),
        H("Optimal phases for two complex columns"),
        Blocks(
            Describe.Lean(DescribeId.Create("phases-dominate"), DeclarationHandle.Create(Module + ".phases_dominate"),
                H("A scalar phase family dominates a vector family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite index type, real coefficients r and s, and complex unit phases z, take vectors v of norm at most one in any complex inner product space. "
                    + "The two-column length is the square root of the sum of squared norms of r times the sum of v and s times the sum of z times v. "
                    + "There is a scalar unit phase at each index whose two-column length is at least as large. "
                    + "Cauchy–Schwarz bounds the length by a normalized two-column dual. Keeping its off-diagonal Gram entry fixed, move the diagonal mass to the determinant-zero endpoint selected by the sign of r²−s². "
                    + "Aligning scalar phases attains the resulting bound, including when a dual pairing vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("optimal-phases"), DeclarationHandle.Create(Module + ".optimal_phases"),
                H("A single phase family bounds every vector family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite product of unit circles is compact and the scalar objective is continuous. A maximizing phase family therefore bounds the two-column length of every admissible vector family in every complex inner product space."))),
                DescribeRole.Theorem))));
}
