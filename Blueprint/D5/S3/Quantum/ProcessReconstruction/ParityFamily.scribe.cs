using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class ParityFamilyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/ParityFamily";
    private static readonly LibraryNoteRef Horodecki = LibraryNoteRef.Create("D5/L/ProcessReconstruction/horodecki2003entanglement");
    private static readonly LibraryNoteRef Karnin = LibraryNoteRef.Create("D5/L/ProcessReconstruction/karnin1983secret");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit unital entanglement-breaking pair agrees on every proper output marginal and has diamond distance two.",
        H("Parity Obstruction to Local-Output Reconstruction"),
        Blocks(
            Paragraph(Text(
                "On any finite qubit register with a chosen input site i, both channels measure "
                + "the global input in the computational basis. The first prepares the uniform "
                + "diagonal state on the parity class specified by input bit i. The second "
                + "interchanges the parity classes. This gives the claimed failure of the "
                + "single-output reconstruction implication for every register with at least "
                + "two sites.")),
            Describe.Lean(DescribeId.Create("parity-measure-prepare"),
                DeclarationHandle.Create(Module + ".parityChannel_measure_prepare"),
                H("Measure-and-prepare form on the full input algebra"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Horodecki, Karnin),
                Blocks(Paragraph(Text(
                    "For each choice of i and either flip, the channel has positive measurement "
                    + "effects summing to the identity and density states as preparations. On "
                    + "every complex input matrix the output is the sum of these states weighted "
                    + "by the trace pairings with the effects. By Horodecki, Shor and Ruskai, "
                    + "Theorem 2, this is the entanglement-breaking characterization."))),
                DescribeRole.Proposition),
            Describe.Lean(DescribeId.Create("parity-unital"),
                DeclarationHandle.Create(Module + ".parityChannel_unital"),
                H("Each parity channel fixes the identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Karnin),
                Blocks(Paragraph(Text(
                    "Each computational input bit value occurs equally often in the identity. "
                    + "The opposite parity weights therefore cancel in each output diagonal entry."))),
                DescribeRole.Proposition),
            Describe.Lean(DescribeId.Create("proper-marginals-agree"),
                DeclarationHandle.Create(Module + ".parityChannel_proper_marginals"),
                H("All proper output marginal channels coincide"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Karnin),
                Blocks(Paragraph(Text(
                    "For every proper subset of the output sites, partial trace onto that subset "
                    + "gives equal channels with the entire global input. A toggle at a discarded "
                    + "site pairs the opposite parities, leaving the same uniform reduced output. "
                    + "Channel equality also gives equality after arbitrary finite reference amplification."))),
                DescribeRole.Proposition),
            Describe.Lean(DescribeId.Create("parity-maximal-distance"),
                DeclarationHandle.Create(Module + ".parityChannel_maximal_diamond"),
                H("Their global unhalved diamond distance is two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Horodecki, Karnin),
                Blocks(Paragraph(Text(
                    "The all-zero computational basis input makes the output supports disjoint, "
                    + "so their trace distance reaches the universal upper bound of two already "
                    + "with a one-dimensional reference. The diamond distance allows every finite "
                    + "reference. The Lean statement requires only a chosen site."))),
                DescribeRole.Proposition))));
}
