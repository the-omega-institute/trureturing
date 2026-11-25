using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class ReconstructionChannelsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite reduced conjugation channels and reference-amplified trace pairings.",
        H("Reduced Unitary Channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("reduced-conjugation"),
                DeclarationHandle.Create(Module + ".reducedConjugation"),
                H("Unitary evolution followed by output restriction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite basis with an equivalence to a product of discarded and kept "
                    + "coordinates, apply unitary conjugation on the entire input and trace out the "
                    + "discarded output coordinates. The result is a canonical quantum channel "
                    + "from the entire input to the kept output."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-lift-observable"),
                DeclarationHandle.Create(Module + ".trace_liftObservable"),
                H("Partial trace and lifted observables are dual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary finite reference coordinates, pairing the reduced joint matrix "
                    + "with an observable on the reference and kept output equals pairing the "
                    + "global joint matrix with its observable lift. The identity holds on complex "
                    + "matrices by expanding the two traces and reindexing the sums."))),
                DescribeRole.Lemma))));
}
