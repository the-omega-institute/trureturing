using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class GridBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual grid boundary deficiency and forming bound", H("Actual grid boundary deficiency and forming bound"),
        Blocks(Paragraph(Text("The actual Cartesian graph degree counts all four missing directions separately, including coincident endpoints in width-one paths. For positive dimensions total deficiency is exactly twice each dimension. The general degree-capacity theorem proves the selected-deficiency estimate seven times the selection size plus its actual isolates at most four times the order plus selected deficiency, and its perimeter consequence. No coloring or representative equality follows from this forming bound.")),
            Node("degree_formula", "degree formula", "Exact declaration: theorem degree_formula {m n : ℕ} (v : Fin m × Fin n) : DegreeCapacity.degree (graph m n) v= (if v.1.val=0 then 0 else 1)+(if v.1.val+1=m then 0 else 1)+ (if v.2.val=0 then 0 else 1)+(if v.2.val+1=n then 0 else 1).", DescribeRole.Theorem),
            Node("degree_le_four", "degree le four", "Exact declaration: theorem degree_le_four {m n : ℕ} (v : Fin m × Fin n) : DegreeCapacity.degree (graph m n) v≤4.", DescribeRole.Theorem),
            Node("total_deficiency", "total deficiency", "Exact declaration: theorem total_deficiency {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : DissociationDeficiency.deficiency (graph m n) 4 Finset.univ=2*m+2*n.", DescribeRole.Theorem),
            Node("selected_deficiency_bound", "selected deficiency bound", "Exact declaration: theorem selected_deficiency_bound {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (S : Finset (Fin m × Fin n)) : DissociationDeficiency.deficiency (graph m n) 4 S≤2*m+2*n.", DescribeRole.Theorem),
            Node("forming_bound", "forming bound", "Exact declaration: theorem forming_bound {m n : ℕ} (S : Finset (Fin m × Fin n)) (hS : IsMinimalStarForming (graph m n) 2 S) : 7*S.card+(isolates (graph m n) S).card≤4*(m*n)+ DissociationDeficiency.deficiency (graph m n) 4 S.", DescribeRole.Theorem),
            Node("forming_perimeter_bound", "forming perimeter bound", "Exact declaration: theorem forming_perimeter_bound {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (S : Finset (Fin m × Fin n)) (hS : IsMinimalStarForming (graph m n) 2 S) : 7*S.card+(isolates (graph m n) S).card≤4*(m*n)+2*m+2*n.", DescribeRole.Theorem)), []));
}
