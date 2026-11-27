using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanShellMellinDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanShellMellin";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mellin continuation of scaled Möbius shell sums",
        H("Mellin continuation of scaled Möbius shell sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-forces-kernel-zero"),
                DeclarationHandle.Create(Owner + ".zero_forces_kernel_zero"),
                H("Zeros of zeta force zeros of the test transform"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A continuous complex test W vanishing outside (1, 2) gives the scaled sum of μ(n)W(nt). Multiplication of its Mellin transform by zeta recovers the test transform by absolute convergence for Re(s) > 1. The square-root bound with arbitrary positive slack continues the identity across the punctured right half-strip and forces the test transform to vanish at each zero there."))),
                DescribeRole.Theorem))));
}
