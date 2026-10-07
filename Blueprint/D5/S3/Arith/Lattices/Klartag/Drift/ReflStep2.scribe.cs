using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class ReflStep2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Refl Step2"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate refl step2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "reflStep2", "refl Step2",
                "The reflected step, *defined* through the past.", DescribeRole.Definition),
            Node("claim-2", "reflStep2_eq_reflStep", "refl Step2 eq refl Step",
                "The bridge. Fresh definition on the left; the frozen reflStep is one delta step away.", DescribeRole.Theorem),
            Node("claim-3", "reflOf_past_eq_reflStep", "refl Of past eq refl Step",
                "The same at an index j < k, against the past truncated at k.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
