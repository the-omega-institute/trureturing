using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReverseDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReverseDecoder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-dimensional reverse instance with the literal twelve-dimensional source environment.",
        H("An explicit source amplitude"),
        Blocks(
            Paragraph(Text("The input is a qubit, the output is a qubit times a three-level system, and the source environment is the input times a copy of that output. The active amplitude is Y = 3I + sigma-x tensor diag(1,-1,0) + sigma-z tensor (E02+E20). The source permutation exchanges the reference qubit and the binary output coordinate. The unused environment coordinates are retained.")),
            Entry("physical", "physical_channel", "The physical channel",
                "The explicitly specified twelve-label Kraus family is normalized and defines a completely positive, trace-preserving map in the canonical quantum-channel interface. Its output on the maximally mixed qubit is Y squared divided by 62."),
            Entry("rotation", "rotation_unitary", "The active rotation",
                "The four real rotation parameters satisfy two unit-circle equations. These equations imply both unitary identities for the active six-dimensional matrix."),
            Entry("rows", "supported_rows", "Literal source rows",
                "After adjoining the fixed zero ancilla, the actual source permutation maps every physical output into the active six-dimensional source support. The composite source Kraus operators are the active rotation rows; all other environment labels give zero."),
            Entry("sos", "gap_positive", "A positive polynomial gap",
                "Under the two circle equations and a strictly positive sum of sine parameters, the displayed sum-of-squares certificate gives a strictly positive polynomial gap. This statement alone does not identify either decoder fidelity. The positive polar product, the ordinary Petz identity, and the canonical-purification comparison are additional mathematical obligations."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
