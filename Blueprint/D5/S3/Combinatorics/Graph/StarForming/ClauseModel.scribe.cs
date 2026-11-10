using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClauseModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClauseModel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact binary private-clause optimization", H("Exact binary private-clause optimization"),
        Blocks(Paragraph(Text("Duplicate-free actual closed-neighborhood and oriented-edge clauses characterize minimal two-star formation by hitting and singleton private intersections. The displayed binary integer constraints are equivalent to that predicate, including empty graphs and isolated vertices. The objective has an actual feasible optimizer of value SF and bounds every feasible selection. No solver result is used.")),
            Node("closed", "closed", "Exact declaration: def closed (u : V) : Finset V.", DescribeRole.Definition),
            Node("oriented", "oriented", "Exact declaration: def oriented (u v : V) : Finset V.", DescribeRole.Definition),
            Node("clauses", "clauses", "Exact declaration: def clauses : Finset (Finset V).", DescribeRole.Definition),
            Node("clause_nonempty", "clause nonempty", "Exact declaration: theorem clause_nonempty (E : Finset V) (hE : E ∈ clauses G) : E.Nonempty.", DescribeRole.Theorem),
            Node("minimal_iff_private", "minimal iff private", "Exact declaration: theorem minimal_iff_private (S : Finset V) : IsMinimalStarForming G 2 S ↔ (∀ E ∈ clauses G, (S ∩ E).Nonempty) ∧ ∀ v ∈ S, ∃ E ∈ clauses G, S ∩ E = {v}.", DescribeRole.Theorem),
            Node("bit", "bit", "Exact declaration: def bit (b : Bool) : ℕ.", DescribeRole.Definition),
            Node("Feasible", "Feasible", "Exact declaration: def Feasible (S : Finset V) (p : Finset V → Bool) : Prop.", DescribeRole.Definition),
            Node("feasible_iff_minimal", "feasible iff minimal", "Exact declaration: theorem feasible_iff_minimal (S : Finset V) : (∃ p, Feasible G S p) ↔ IsMinimalStarForming G 2 S.", DescribeRole.Theorem),
            Node("objective_attained", "objective attained", "Exact declaration: theorem objective_attained : (∃ S p, Feasible G S p ∧ S.card = SF G 2) ∧ ∀ S p, Feasible G S p → S.card ≤ SF G 2.", DescribeRole.Theorem)), []));
}
