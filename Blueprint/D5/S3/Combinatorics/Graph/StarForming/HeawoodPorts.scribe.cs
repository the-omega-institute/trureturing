using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodPortsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Saturated ports in the actual broken Heawood block", H("Saturated ports in the actual broken Heawood block"),
        Blocks(Paragraph(Text("The original fourteen-vertex broken incidence graph is retained with its exact sparse neighbor rows. Bounded kernel chunks prove that every actual dissociation selection has at most eight vertices; every eight-set contains both ports, each with exactly one selected internal neighbor. The original eight-set and port-omitting seven-set attain their exact sizes. The certificate is local to one fixed block; arbitrary family conclusions are proved by its consumers, without enumerating family size.")),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 14).", DescribeRole.Definition),
            Node("facts", "facts", "Exact declaration: theorem facts (D : Finset (Fin 14)) (hD : IsKIndependent graph 2 D) : D.card ≤ 8 ∧ (D.card = 8 → 0 ∈ D ∧ 8 ∈ D ∧ DegreeCapacity.selectedDegree graph D 0 = 1 ∧ DegreeCapacity.selectedDegree graph D 8 = 1).", DescribeRole.Theorem),
            Node("eightSet", "eightSet", "Exact declaration: def eightSet : Finset (Fin 14).", DescribeRole.Definition),
            Node("sevenSet", "sevenSet", "Exact declaration: def sevenSet : Finset (Fin 14).", DescribeRole.Definition),
            Node("selections", "selections", "Exact declaration: theorem selections : IsKIndependent graph 2 eightSet ∧ eightSet.card = 8 ∧ IsKIndependent graph 2 sevenSet ∧ sevenSet.card = 7 ∧ 0 ∉ sevenSet ∧ 8 ∉ sevenSet.", DescribeRole.Theorem)), []));
}
