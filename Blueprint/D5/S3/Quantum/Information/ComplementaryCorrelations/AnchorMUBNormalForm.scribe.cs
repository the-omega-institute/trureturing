using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class AnchorMUBNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduction of local mutually unbiased measurement pairs.",
        H("Reduction of local mutually unbiased measurement pairs"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-anchormubnormalform-anchorquadraticin-eq-standard"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalForm.anchorQuadraticIn_eq_standard"),
                H("Standard measurements on the transported data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reduce each relative basis unitary up to row and column phases and permutations. The full quadratic equals the standard computational, Hadamard and Fourier expression on the locally conjugated product state and tangent."))), DescribeRole.Theorem))));
}
