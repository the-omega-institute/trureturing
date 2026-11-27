using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanFixedRationalKernelMellinDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mellin transform of the rational cubic kernel",
        H("Mellin transform of the rational cubic kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mellin-formula"),
                DeclarationHandle.Create(Owner + ".mellin_formula"),
                H("Exact Mellin product"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the half-plane Re(s) > 0, the transform of the real kernel is the product of a^(s+j) − 1 from j = 0 through 3 divided by s(s+1)(s+2)(s+3), with a = 7/6. Integration on each truncated cubic gives endpoint terms whose upper contributions cancel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mellin-ne-zero"),
                DeclarationHandle.Create(Owner + ".mellin_ne_zero"),
                H("Nonvanishing in the right half-plane"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each power a^(s+j) has modulus a^(Re(s)+j) > 1 in this half-plane, and the four denominator factors are nonzero."))),
                DescribeRole.Theorem))));
}
