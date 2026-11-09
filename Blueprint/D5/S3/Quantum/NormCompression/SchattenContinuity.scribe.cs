using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class SchattenContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing actual Schatten trace and continuity proofs are shared by the finite power supplier and the original strict spectral consumer.",
        H("Shared Schatten continuity"), Blocks(
            Describe.Lean(DescribeId.Create("schatten-continuity-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/SchattenContinuity.schattenPow_trace"),
                H("Actual column Gram trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural square dimension, including zero, and every positive real p, the actual singular value power sum equals the real trace of the p/2-th functional calculus power of A* A. This exact proof was extracted from StrictSpectralPolyaRefutation and is reused without reproving it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("schatten-continuity-continuous"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/SchattenContinuity.continuous_schattenPow"),
                H("Continuity of actual Schatten powers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive real exponent the actual Schatten power is continuous on square complex matrices, including the zero dimension. The original strict spectral consumer and the finite power trace supplier both import this existing proof. The extraction adds no new continuity assertion or literature novelty claim."))), DescribeRole.Theorem))));
}
