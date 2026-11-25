using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzPhysicalQubitRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized square root of a physical flag.",
        H("Normalized square root of a physical flag"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unscaledblock-posdef"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.unscaledBlock_posDef"),
                H("Faithful flag block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive determinant and positive first diagonal entry give a triangular factorization of the unscaled flag block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalizedroot-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.normalizedRoot_formula"),
                H("Exact normalized square root"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace and determinant identities for the positive qubit square root determine its scalar denominator and all four entries after the marginal normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalizedroot-firstvariation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.normalizedRoot_firstVariation"),
                H("Derivative at the diagonal flag"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The determinant and denominator have zero derivative at the base. The upper and lower off-diagonal entries have different slopes because the inverse half-power acts on the right."))),
                DescribeRole.Theorem))));
}
