using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six original double-lift certificates", H("The six original double-lift certificates"),
        Blocks(Paragraph(Text("The supplied binary point/line labels, sheet bits, twist flags and selected lists are unchanged. All six N1,N2,S,J,C,K types have actual dissociation fifteen-sets and the cubic upper cap sixteen; S and J additionally have actual sixteen-sets proving beta=SF=16. The six finite witnesses do not themselves classify arbitrary signings or transfer across graph isomorphisms.")),
            Node("label", "label", "Exact declaration: def label (vertex : Fin 28) : Nat.", DescribeRole.Definition),
            Node("sheet", "sheet", "Exact declaration: def sheet (vertex : Fin 28) : Nat.", DescribeRole.Definition),
            Node("dot", "dot", "Exact declaration: def dot (first second : Nat) : Nat.", DescribeRole.Definition),
            Node("adjacency", "adjacency", "Exact declaration: def adjacency (twists : List (Nat × Nat)) (first second : Fin 28) : Prop.", DescribeRole.Definition),
            Node("selected", "selected", "Exact declaration: def selected (points lines : List Nat) (vertex : Fin 28) : Prop.", DescribeRole.Definition),
            Node("scalarTwists", "scalarTwists", "Exact declaration: def scalarTwists : List (Nat × Nat).", DescribeRole.Definition),
            Node("jordanTwists", "jordanTwists", "Exact declaration: def jordanTwists : List (Nat × Nat).", DescribeRole.Definition),
            Node("scalarPoints", "scalarPoints", "Exact declaration: def scalarPoints : List Nat.", DescribeRole.Definition),
            Node("scalarLines", "scalarLines", "Exact declaration: def scalarLines : List Nat.", DescribeRole.Definition),
            Node("jordanPoints", "jordanPoints", "Exact declaration: def jordanPoints : List Nat.", DescribeRole.Definition),
            Node("jordanLines", "jordanLines", "Exact declaration: def jordanLines : List Nat.", DescribeRole.Definition),
            Node("scalar_dissociates", "scalar dissociates", "Exact declaration: theorem scalar_dissociates : Dissociates (adjacency scalarTwists) (selected scalarPoints scalarLines).", DescribeRole.Theorem),
            Node("jordan_dissociates", "jordan dissociates", "Exact declaration: theorem jordan_dissociates : Dissociates (adjacency jordanTwists) (selected jordanPoints jordanLines).", DescribeRole.Theorem),
            Node("scalar_card", "scalar card", "Exact declaration: theorem scalar_card : ((List.finRange 28).filter (fun vertex => decide (selected scalarPoints scalarLines vertex))).length = 16.", DescribeRole.Theorem),
            Node("jordan_card", "jordan card", "Exact declaration: theorem jordan_card : ((List.finRange 28).filter (fun vertex => decide (selected jordanPoints jordanLines vertex))).length = 16.", DescribeRole.Theorem),
            Node("scalarGraph", "scalarGraph", "Exact declaration: def scalarGraph : SimpleGraph (Fin 28).", DescribeRole.Definition),
            Node("jordanGraph", "jordanGraph", "Exact declaration: def jordanGraph : SimpleGraph (Fin 28).", DescribeRole.Definition),
            Node("scalarSet", "scalarSet", "Exact declaration: def scalarSet : Finset (Fin 28).", DescribeRole.Definition),
            Node("jordanSet", "jordanSet", "Exact declaration: def jordanSet : Finset (Fin 28).", DescribeRole.Definition),
            Node("scalar_selection", "scalar selection", "Exact declaration: theorem scalar_selection : IsKIndependent scalarGraph 2 scalarSet ∧ scalarSet.card = 16.", DescribeRole.Theorem),
            Node("jordan_selection", "jordan selection", "Exact declaration: theorem jordan_selection : IsKIndependent jordanGraph 2 jordanSet ∧ jordanSet.card = 16.", DescribeRole.Theorem),
            Node("scalar_class", "scalar class", "Exact declaration: theorem scalar_class : scalarGraph.Colorable 2 ∧ ∀ v, DegreeCapacity.degree scalarGraph v = 3.", DescribeRole.Theorem),
            Node("jordan_class", "jordan class", "Exact declaration: theorem jordan_class : jordanGraph.Colorable 2 ∧ ∀ v, DegreeCapacity.degree jordanGraph v = 3.", DescribeRole.Theorem),
            Node("scalar_parameters", "scalar parameters", "Exact declaration: theorem scalar_parameters : beta scalarGraph 2 = 16 ∧ SF scalarGraph 2 = 16.", DescribeRole.Theorem),
            Node("jordan_parameters", "jordan parameters", "Exact declaration: theorem jordan_parameters : beta jordanGraph 2 = 16 ∧ SF jordanGraph 2 = 16.", DescribeRole.Theorem),
            Node("sixTwists", "sixTwists", "Exact declaration: def sixTwists (k : Fin 6) : List (Nat × Nat).", DescribeRole.Definition),
            Node("sixPoints", "sixPoints", "Exact declaration: def sixPoints (k : Fin 6) : List Nat.", DescribeRole.Definition),
            Node("sixLines", "sixLines", "Exact declaration: def sixLines (k : Fin 6) : List Nat.", DescribeRole.Definition),
            Node("sixGraph", "sixGraph", "Exact declaration: def sixGraph (k : Fin 6) : SimpleGraph (Fin 28).", DescribeRole.Definition),
            Node("sixSet", "sixSet", "Exact declaration: def sixSet (k : Fin 6) : Finset (Fin 28).", DescribeRole.Definition),
            Node("six_selection", "six selection", "Exact declaration: theorem six_selection (k : Fin 6) : IsKIndependent (sixGraph k) 2 (sixSet k) ∧ (sixSet k).card = 15.", DescribeRole.Theorem),
            Node("six_class", "six class", "Exact declaration: theorem six_class (k : Fin 6) : (sixGraph k).Colorable 2 ∧ ∀ v, DegreeCapacity.degree (sixGraph k) v = 3.", DescribeRole.Theorem),
            Node("six_beta_bounds", "six beta bounds", "Exact declaration: theorem six_beta_bounds (k : Fin 6) : 15 ≤ beta (sixGraph k) 2 ∧ beta (sixGraph k) 2 ≤ 16.", DescribeRole.Theorem)), []));
}
