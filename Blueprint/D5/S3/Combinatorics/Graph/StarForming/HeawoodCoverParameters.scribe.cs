using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodCoverParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Star-forming and disconnected-lift parameters", H("Star-forming and disconnected-lift parameters"),
        Blocks(Paragraph(Text("An explicit isomorphism separates cyclic Heawood labels from binary incidence labels. Every signing has SF sixteen. Disconnected signings have beta fourteen by disjoint-union additivity.")),
            Node("cyclicIso", "cyclicIso", "Exact declaration: def cyclicIso : HeawoodParameters.graph ≃g base.", DescribeRole.Definition),
            Node("base_regular", "base regular", "Exact declaration: theorem base_regular : ∀ v, DegreeCapacity.degree base v=3.", DescribeRole.Theorem),
            Node("sf_all", "sf all", "Exact declaration: theorem sf_all (s : Signing) : SF (graph s) 2=16.", DescribeRole.Theorem),
            Node("pack", "pack", "Exact declaration: def pack : (Fin 14 × F2) ≃ Fin 28.", DescribeRole.Definition),
            Node("disconnected_beta", "disconnected beta", "Exact declaration: theorem disconnected_beta (s : Signing) (hs : ¬ (graph s).Preconnected) : beta (graph s) 2=14.", DescribeRole.Theorem)), []));
}
