using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClauseSizesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The subcubic model size", H("The subcubic model size"),
        Blocks(Paragraph(Text("The actual duplicate-free clause family has at most (d+1)n members at maximum degree d. In a subcubic graph each clause has at most five vertices; the exact binary model uses at most 5n variables and 9n displayed constraints. These counts refer to the actual clause sets and feasibility predicate in ClauseModel.")),
            Node("clauses_card_le", "clauses card le", "Exact declaration: theorem clauses_card_le (d : ℕ) (hd : ∀ v, DegreeCapacity.degree G v ≤ d) : (clauses G).card ≤ (d+1)*Fintype.card V.", DescribeRole.Theorem),
            Node("subcubic_clause_size", "subcubic clause size", "Exact declaration: theorem subcubic_clause_size (hd : ∀ v, DegreeCapacity.degree G v ≤ 3) (E : Finset V) (hE : E ∈ clauses G) : E.card ≤ 5.", DescribeRole.Theorem),
            Node("subcubic_model_size", "subcubic model size", "Exact declaration: theorem subcubic_model_size (hd : ∀ v, DegreeCapacity.degree G v ≤ 3) : (clauses G).card ≤ 4*Fintype.card V ∧ Fintype.card V + (clauses G).card ≤ 5*Fintype.card V ∧ 2*(clauses G).card + Fintype.card V ≤ 9*Fintype.card V.", DescribeRole.Theorem)), []));
}
