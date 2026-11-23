using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DeltaY;

internal sealed class TwoColorInvariantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant.";
    private static readonly LibraryNoteRef Zhou =
        LibraryNoteRef.Create("D5/L/Rewriting/zhou2026deltay");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-color invariant forces strong reverse moves above the minimum-degree threshold.",
        H("The two-color invariant"),
        Blocks(
            Describe.Lean(DescribeId.Create("delta-y-strong-degree-six"),
                DeclarationHandle.Create(Prefix + "source_degree_six_histories"),
                H("Strong reachability at minimum degree six"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Zhou),
                Blocks(
                    Paragraph(Text("Initially all vertices have the same color. Edges joining different colors weigh two and same-color edges weigh one. The invariant requires weighted degree at least six at each active vertex, monochromatic triangles, and absence of an all-crossing four-cycle.")),
                    Paragraph(Text("A forward move colors the new center opposite the triangle. A reverse move preserves the colors of the surviving vertices. In either case, affected survivors exchange weight two for weight two. The triangle and four-cycle conditions prevent a new mixed triangle or a new all-crossing four-cycle.")),
                    Paragraph(Text("Induction over the ordinary history gives a strong history with the same successive graphs. The reflexive case is the empty history."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("delta-y-reachable-reverse-independent"),
                DeclarationHandle.Create(Prefix + "source_reachable_reverse_independent"),
                H("Independence at every reachable reverse site"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Zhou),
                Blocks(Paragraph(Text("A center with degree three must have three crossing incident edges to attain weighted degree six. An edge between two of its neighbors would give a mixed triangle. The neighbors therefore form an independent triple."))),
                DescribeRole.Theorem)),
        []));
}
