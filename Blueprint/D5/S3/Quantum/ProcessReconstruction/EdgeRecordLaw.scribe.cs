using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class EdgeRecordLawDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent fair edge and site bits give uniform output laws on every proper subset of an open path.",
        H("Finite Edge Record Laws"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-record-kernel-all-ones"),
                DeclarationHandle.Create(Module + ".kernel_allOn"),
                H("The all-ones input selects a parity class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "On a path with N = n + 1 sites, each active site outputs the XOR of the two "
                    + "adjacent edge bits, with zero at missing edges and a shift by b at site zero. "
                    + "An inactive site outputs its own fair bit. Prefix XOR, after removing the "
                    + "endpoint shift, recovers the edge bits from the full parity word. The "
                    + "all-ones row is uniform on parity b. Every other row is uniform on all words. "
                    + "The underlying adjacent XOR parity sampler appears in Horacsek et al., "
                    + "Local Samplers for Product Distributions, Section 1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-kernel-marginal"),
                DeclarationHandle.Create(Module + ".kernel_marginal"),
                H("Every proper output law is uniform for every input"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "For a proper site mask, fixing the visible coordinates of a parity word leaves "
                    + "one unseen coordinate available to enforce parity. All fibers therefore have "
                    + "the same size. Inactive coordinates contribute independent fair bits."))),
                DescribeRole.Theorem))));
}
