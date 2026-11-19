using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal interfaces preserve two-connectivity", H("Reciprocal interfaces preserve two-connectivity"),
        Blocks(Paragraph(Text("The actual broken Heawood block stays connected after any vertex deletion. Reciprocal opposite-port edges lift every preconnected loopless interaction graph to a graph connected before and after each vertex deletion, with order at least three for a nonempty finite index type. The actual loop-aware independence maximum reduces to the ordinary independent-set maximum, giving exact SF and beta. Degree, cyclic girth and nonplanarity are separate assertions.")),
            Node("broken_delete_preconnected", "broken delete preconnected", "Exact declaration: theorem broken_delete_preconnected (z : Fin 14) : (HeawoodPorts.graph.induce {a | a ≠ z}).Preconnected.", DescribeRole.Theorem),
            Node("broken_preconnected", "broken preconnected", "Exact declaration: theorem broken_preconnected : HeawoodPorts.graph.Preconnected.", DescribeRole.Theorem),
            Node("reciprocal", "reciprocal", "Exact declaration: def reciprocal {I : Type} (Q : SimpleGraph I) : SimpleGraph (I × Fin 2).", DescribeRole.Definition),
            Node("reciprocal_bipartite", "reciprocal bipartite", "Exact declaration: theorem reciprocal_bipartite {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) : (graph (reciprocal Q)).Colorable 2.", DescribeRole.Theorem),
            Node("reciprocal_delete_preconnected", "reciprocal delete preconnected", "Exact declaration: theorem reciprocal_delete_preconnected {I : Type} (Q : SimpleGraph I) (hQ : Q.Preconnected) (z : I × Fin 14) : ((graph (reciprocal Q)).induce {x | x ≠ z}).Preconnected.", DescribeRole.Theorem),
            Node("reciprocal_preconnected", "reciprocal preconnected", "Exact declaration: theorem reciprocal_preconnected {I : Type} (Q : SimpleGraph I) (hQ : Q.Preconnected) : (graph (reciprocal Q)).Preconnected.", DescribeRole.Theorem),
            Node("reciprocal_two_connected", "reciprocal two connected", "Exact declaration: theorem reciprocal_two_connected {I : Type} [Fintype I] [Nonempty I] (Q : SimpleGraph I) (hQ : Q.Preconnected) : (graph (reciprocal Q)).Connected ∧ (∀ z : I × Fin 14, ((graph (reciprocal Q)).induce {x | x ≠ z}).Connected) ∧ 3 ≤ Fintype.card (I × Fin 14).", DescribeRole.Theorem),
            Node("reciprocal_interaction", "reciprocal interaction", "Exact declaration: theorem reciprocal_interaction {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) (i j : I) : interaction (reciprocal Q) i j ↔ Q.Adj i j.", DescribeRole.Theorem),
            Node("reciprocal_alpha0", "reciprocal alpha0", "Exact declaration: theorem reciprocal_alpha0 {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) : alpha0 (reciprocal Q) = Q.indepNum.", DescribeRole.Theorem),
            Node("reciprocal_sf_beta", "reciprocal sf beta", "Exact declaration: theorem reciprocal_sf_beta {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) : StarFormingDissociationRefutation.SF (graph (reciprocal Q)) 2 = 8*Fintype.card I ∧ StarFormingDissociationRefutation.beta (graph (reciprocal Q)) 2 = 7*Fintype.card I + Q.indepNum.", DescribeRole.Theorem)), []));
}
