using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.JainAbsCosine;

internal sealed class ForcedZerosDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite frequency support of low even powers.",
        H("Forced Fourier zeros"), Blocks(
            Describe.Lean(DescribeId.Create("jain-even-mode-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros.modeValue_even_eq_zero"),
                H("Modes beyond the even power support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural s,j,m with s less than j and j at most m, the real Fourier mode at exponent 2s vanishes. A finite cosine sum gives the initial constant-power case. Multiplication by the squared cosine shifts a frequency by at most one; induction preserves vanishing beyond the support. The argument includes s=0 and does not require the odd order to be prime."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-even-gap-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros.modeValue_gap_even_eq_zero"),
                H("Simultaneous zeros of mode differences"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any natural step d, if s is less than j and j+d is at most m, the difference of modes j and j+d vanishes at exponent 2s. Both modes lie beyond the same finite frequency support. The steps one and two used for spectral separation are included."))),
                DescribeRole.Theorem))));
}
