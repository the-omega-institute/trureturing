using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class BargmannKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Hilbert sections of the completed kernel.",
        H("Actual Hilbert sections of the completed kernel"),
        Blocks(Describe.Lean(DescribeId.Create("completed-two-mode-bargmann-sections"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/BargmannKernel.kernel_eq_transform_discarded_section"),
            H("Actual Hilbert sections of the completed kernel"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The two-mode carrier is lp(Natural -> H,2), with H=lp(Natural -> Complex,2). Each evaluation section is constructed as an actual H vector by continuous coordinate functionals or an absolutely convergent H-valued contraction. The kernel is the Bargmann transform of that genuine section.")),
                Paragraph(Text("The kernel agrees with the inner product against the actual two-mode exponential vector, with the conjugation convention explicit. Its absolute value is bounded by norm(V)*exp((norm(z)^2+norm(w)^2)/2). Both scalar-variable sections are entire, and the transform is injective on the completed two-mode carrier.")),
                Paragraph(Text("The discarded and retained contractions obey the corresponding one-variable exponential norm bounds. Tensor inputs give the product of their actual Bargmann transforms. These joins are used to reconstruct finite-rank Hilbert factors from arbitrary entire separated factors; arbitrary entire functions are not assumed to be in the Bargmann image."))),
            DescribeRole.Theorem))));
}

