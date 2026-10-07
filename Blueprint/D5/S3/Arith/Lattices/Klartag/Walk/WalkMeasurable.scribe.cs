using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class WalkMeasurableDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Walk Measurable"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate walk measurable to the stochastic ellipsoid construction.")),
            Node("claim-2", "measurable_pureWalk", "measurable pure Walk",
                "The pure walk is measurable — the increment reads the active set through the projection.", DescribeRole.Theorem),
            Node("claim-3", "measurable_constraintM", "measurable constraint M",
                "WalkTelescope.hprop_of_hincl's hM.", DescribeRole.Theorem),
            Node("claim-4", "chain_eq_of_eq", "chain eq of eq",
                "The chain reads only the increments before time k.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
