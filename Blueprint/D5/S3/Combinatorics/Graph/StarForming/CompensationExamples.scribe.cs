using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CompensationExamplesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected balanced-accounting counterexample", H("Connected balanced-accounting counterexample"),
        Blocks(Paragraph(Text("The exact source twenty-eight-vertex graph and sixteen-set are kept. Actual deletion failures prove minimality, explicit paths prove connectivity, and kernel checks prove cubic bipartiteness, balanced isolates, the high path, zero witness surplus and the unused resource counts. The source normal-form lists swap leaves8 and10 and resources9 and11: in the stated graph9 has selected degree one and11 degree two. The canonical extraction uses reserved leaf8, extra leaf10 and high witness0-to9. The actual two original unaugmented exchanges each have size fourteen; the unchanged source dissociation fifteen-set makes both nonmaximum and forces compensation slack at least two. The typed closed claim/result pair refutes the candidate maximum-exchange inference. No exact beta upper bound, optimizer result or claim about the later augmented exchanges is made.")),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (v : Fin 28) : List (Fin 28).", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 28).", DescribeRole.Definition),
            Node("selection", "selection", "Exact declaration: def selection : Finset (Fin 28).", DescribeRole.Definition),
            Node("unaugmentedLeft", "unaugmentedLeft", "Exact declaration: def unaugmentedLeft : Finset (Fin 28).", DescribeRole.Definition),
            Node("unaugmentedRight", "unaugmentedRight", "Exact declaration: def unaugmentedRight : Finset (Fin 28).", DescribeRole.Definition),
            Node("largerDissociation", "largerDissociation", "Exact declaration: def largerDissociation : Finset (Fin 28).", DescribeRole.Definition),
            Node("highs", "highs", "Exact declaration: def highs : Finset (Fin 28).", DescribeRole.Definition),
            Node("extraLeaves", "extraLeaves", "Exact declaration: def extraLeaves : Finset (Fin 28).", DescribeRole.Definition),
            Node("color", "color", "Exact declaration: def color (v : Fin 28) : Bool.", DescribeRole.Definition),
            Node("failure", "failure", "Exact declaration: def failure (v : Fin 28) : Fin 28.", DescribeRole.Definition),
            Node("minimal", "minimal", "Exact declaration: theorem minimal : IsMinimalStarForming graph 2 selection.", DescribeRole.Theorem),
            Node("class_and_balance", "class and balance", "Exact declaration: theorem class_and_balance : (∀ v, degree graph v=3) ∧ (∀ v w, graph.Adj v w → color v≠color w) ∧ isolates graph selection=({24,25} : Finset (Fin 28)) ∧ ((isolates graph selection).filter (fun v => color v=true)).card=1 ∧ ((isolates graph selection).filter (fun v => color v=false)).card=1.", DescribeRole.Theorem),
            Node("preconnected", "preconnected", "Exact declaration: theorem preconnected : graph.Preconnected.", DescribeRole.Theorem),
            Node("high_path", "high path", "Exact declaration: theorem high_path : CertificateBound.high graph selection=highs ∧ (∀ v w : Fin 8, graph.Adj ⟨v.val,by omega⟩ ⟨w.val,by omega⟩ ↔ v.val+1=w.val ∨ w.val+1=v.val) ∧ (highs.filter (fun v => selectedDegree graph selection v=2)).card=4 ∧ (highs.filter (fun v => selectedDegree graph selection v=3)).card=4.", DescribeRole.Theorem),
            Node("zero_accounting", "zero accounting", "Exact declaration: theorem zero_accounting : (∀ h∈highs, 3-selectedDegree graph selection (failure h)= selectedDegree graph selection h-1) ∧ ((Finset.univ\\selection)\\highs.image failure)=({11,23,26,27} : Finset (Fin 28)) ∧ (∀ v∈({11,23} : Finset (Fin 28)), selectedDegree graph selection v=2) ∧ (∀ v∈({26,27} : Finset (Fin 28)), selectedDegree graph selection v=3) ∧ extraLeaves.card=2.", DescribeRole.Theorem),
            Node("exchanges", "exchanges", "Exact declaration: theorem exchanges : IsKIndependent graph 2 unaugmentedLeft ∧ unaugmentedLeft.card=14 ∧ IsKIndependent graph 2 unaugmentedRight ∧ unaugmentedRight.card=14 ∧ IsKIndependent graph 2 largerDissociation ∧ largerDissociation.card=15 ∧ selection.card=16.", DescribeRole.Theorem),
            Node("positive_slack", "positive slack", "Exact declaration: theorem positive_slack : 15≤beta graph 2 ∧ unaugmentedLeft.card<beta graph 2 ∧ unaugmentedRight.card<beta graph 2 ∧ 2≤3*Fintype.card (Fin 28)+2*beta graph 2-7*selection.card.", DescribeRole.Theorem),
            Node("claim", "claim", "Exact declaration: def claim : Prop.", DescribeRole.Definition),
            Node("result", "result", "Exact declaration: theorem result : ¬claim.", DescribeRole.Theorem)), []));
}
