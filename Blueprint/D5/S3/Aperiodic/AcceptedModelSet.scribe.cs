using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Aperiodic;

internal sealed class AcceptedModelSetDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Aperiodic/AcceptedModelSet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissibility predicates separate language-selected model sets from unrestricted lattice-window model sets.",
        H("Admissibility-Selected Model Sets"),
        Blocks(
            Def("accepted", "acceptedModelSet", "Accepted model set",
                "A physical point is selected by a lattice witness satisfying both an internal window condition and an acceptance predicate."),
            Thm("subset", "acceptedModelSet_subset_modelSet", "Accepted sets lie in unrestricted model sets",
                "Dropping the language or cone predicate leaves the ordinary window-selected model set."),
            Thm("window-mono", "acceptedModelSet_window_mono", "Window monotonicity",
                "Enlarging the internal window enlarges the accepted model set."),
            Thm("predicate-mono", "acceptedModelSet_predicate_mono", "Acceptance monotonicity",
                "Weakening the lattice acceptance rule enlarges the selected physical set."),
            Thm("true", "acceptedModelSet_true", "Universal acceptance recovers the model set",
                "The unrestricted model set is the special case in which every lattice point is accepted."),
            Thm("and", "acceptedModelSet_and_of_physical_injective", "Conjunctive acceptance gives intersection",
                "With injective physical projection, conjunction of two acceptance predicates is physical-set intersection."),
            Thm("translate", "acceptedModelSet_translate_lattice", "Shift-invariant acceptance preserves translation",
                "A lattice-shift invariant language or cone retains the exact cut-and-project translation law.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Aperiodic/AlgebraicCutProjectData")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
