using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class GenericBinarySectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Dynamics/Shadowing/GenericBinarySection.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete binary graph languages admit a locally deciding name and a compact first-disagreement section.",
        H("Generic binary names and a convergent section"),
        Blocks(
            Node("generic-name", "Locally deciding binary name", "exists_binary_name_locally_deciding",
                "For every countable family of closed subsets of the binary name space, there is a binary name a such that each family member has an open neighborhood of a contained in it or in its complement. The countability is over the closed family itself.", DescribeRole.Theorem),
            Node("closed-complete-language", "Complete finite graph languages are closed", "initialGraphLanguage_isClosed",
                "A finite directed graph with binary edge data, a continuous finite-alphabet label, and an arbitrary initial vertex set determines a closed set of complete infinite names. The compact space of all complete paths, including the initial restriction, maps continuously to its label image.", DescribeRole.Theorem),
            Node("generic-finite-graphs", "One name decides every finite graph code locally", "exists_generic_finite_graph_decision",
                "Boolean edge, label, and initial-vertex data give a countable family of all finite binary graph languages. A Baire-generic binary name locally decides every language in this family. No restriction on the clopen subsets of another space is imposed.", DescribeRole.Theorem),
            Node("continuous-first-difference", "Continuous first-disagreement map", "continuous_firstDifference",
                "The map from binary names to the one-point compactification of the naturals sends a name to its first disagreement with a fixed name a, and sends a itself to infinity. Finite disagreement fibres are clopen, and agreement on any finite prefix gives continuity at a.", DescribeRole.Theorem),
            Node("compact-section", "A compact convergent section", "exists_firstDifference_section_homeomorph",
                "The set consisting of a and the names obtained by flipping exactly its nth bit is compact. Restricting firstDifference to this set gives a homeomorphism onto the one-point compactification of the naturals.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);
}
