using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClosedRingGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClosedRingGeometry.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced actual selected isolates of closed-high rings", H("Balanced actual selected isolates of closed-high rings"),
        Blocks(Paragraph(Text("The original minimal thirty-six-set in each module has exactly six globally selected isolates, three in each actual bipartition side. Only omitted interface vertices receive external edges, so these are actual assembly isolates. All finite index permutations, including empty and singleton cases, are covered.")),
            Node("isolate_counts", "isolate counts", "Exact declaration: theorem isolate_counts (e : Equiv.Perm I) : let S : Finset (I × Fin 62).", DescribeRole.Theorem)), []));
}
