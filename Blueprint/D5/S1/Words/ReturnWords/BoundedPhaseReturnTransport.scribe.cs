using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class BoundedPhaseReturnTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/ReturnWords/BoundedPhaseReturnTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded phases transport output letters along every actual path.",
        H("Bounded phase return transport"),
        Blocks(
            Proof("path_output_of_bounded_phases", "Path output from bounded phases",
                "A bounded phase certificate fixes the endpoint phase and every output letter "
                + "of each actual finite path. The proof is by induction on the path and "
                + "retains the actual arrow at every step."))));

    private static DocumentBlock Proof(string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}
