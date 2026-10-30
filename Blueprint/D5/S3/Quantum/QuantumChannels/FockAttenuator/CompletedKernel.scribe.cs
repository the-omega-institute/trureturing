using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class CompletedKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed balanced two-photon physical kernel.",
        H("The completed balanced two-photon physical kernel"),
        Blocks(Describe.Lean(DescribeId.Create("actual-balanced-two-photon-kernel"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedKernel.balanced_two_photon_kernel"),
            H("The completed balanced two-photon physical kernel"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every completed Fock input a, the existing beam splitter at transmissivity one half with the actual number-two environment has Bargmann kernel B(a)((z+w)/sqrt(2))*(w-z)^2/(2*sqrt(2)) at every complex pair. The statement uses the existing beamSplitter and tensor definitions.")),
                Paragraph(Text("The forward `beamUnitary` acts on exponential vectors by `rotate(t,r)`. When the unitary is moved through the inner product, its inverse action is `rotate(t,-r)`, so the transform is pulled back by that inverse rotation. This identifies the transform of every completed two-mode input, including arbitrary infinite support. The number-state transform is z^n/sqrt(n!), which gives the exact balanced two-photon normalization.")),
                Paragraph(Text("This is an operator-level physical bridge. It supplies neither an assigned finite matrix spectrum nor a finite-support assumption. Rescaling its two variables and its nonzero scalar preserves the exact number of separated terms, connecting the physical kernel to the quadratic weighted Hankel kernel."))),
            DescribeRole.Theorem))));
}

