using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class TripleGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/TripleGeometry.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced isolates of the triple-port witness", H("Balanced isolates of the triple-port witness"),
        Blocks(Paragraph(Text("The original attaining minimal twenty-eight-per-module selection has exactly four selected isolates per module, two in each actual bipartition side. This statement concerns that displayed selection and asserts no classification of every optimum selection.")),
            Node("isolate_counts", "isolate counts", "Exact declaration: theorem isolate_counts (e : Equiv.Perm I) : let S : Finset (I × Fin 48).", DescribeRole.Theorem)), []));
}
