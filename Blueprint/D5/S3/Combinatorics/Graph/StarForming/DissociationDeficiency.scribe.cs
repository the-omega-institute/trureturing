using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class DissociationDeficiencyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact actual graph deficiency", H("Exact actual graph deficiency"),
        Blocks(Paragraph(Text("For any finite simple graph of maximum degree at most d with d positive, every dissociation set satisfies the exact cut identity with the actual selected isolates, actual complementary edges and degree deficiencies. Dropping nonnegative terms gives the deficiency upper bound. These statements are graph identities, not an assumed port-count certificate.")),
            Node("deficiency", "deficiency", "Exact declaration: def deficiency (d : ℕ) (S : Finset V) : ℕ.", DescribeRole.Definition),
            Node("complementEdges", "complementEdges", "Exact declaration: def complementEdges (S : Finset V) : ℕ.", DescribeRole.Definition),
            Node("exact_identity", "exact identity", "Exact declaration: theorem exact_identity (D : Finset V) (hD : IsKIndependent G 2 D) (d : ℕ) (hdpos : 1≤d) (hd : ∀ v, degree G v≤d) : (2*d-1)*D.card + deficiency G d Finset.univ + (isolates G D).card + 2*complementEdges G D = d*Fintype.card V + 2*deficiency G d D.", DescribeRole.Theorem),
            Node("deficiency_bound", "deficiency bound", "Exact declaration: theorem deficiency_bound (D : Finset V) (hD : IsKIndependent G 2 D) (d : ℕ) (hdpos : 1≤d) (hd : ∀ v, degree G v≤d) : (2*d-1)*D.card + deficiency G d Finset.univ ≤ d*Fintype.card V + 2*deficiency G d D.", DescribeRole.Theorem),
            Node("tight_degrees", "tight degrees", "Exact declaration: theorem tight_degrees (D : Finset V) (hD : IsKIndependent G 2 D) (hi : (isolates G D).card = 0) (he : complementEdges G D = 0) (v : V) : selectedDegree G D v = if v ∈ D then 1 else degree G v.", DescribeRole.Theorem)), []));
}
