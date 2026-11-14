using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CubicCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rewiring away from selected vertices and Fano minimality", H("Rewiring away from selected vertices and Fano minimality"),
        Blocks(Paragraph(Text("Rewiring edges whose endpoints are both outside the fixed selection preserves formation for every smaller selection and therefore inclusion-minimality. The actual fourteen-vertex Fano adjacency table, eight-set and all deletion witnesses are retained with the original cyclic labels. This module proves simplicity, cubic neighbor lists and minimality of that selection; graph invariant upper maxima are established in HeawoodParameters.")),
            Node("forms_rewiring", "forms rewiring", "Exact declaration: theorem forms_rewiring {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection smaller : Vertex → Prop) (hsubset : ∀ vertex, smaller vertex → selection vertex) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) (hforms : Forms original smaller) : Forms modified smaller.", DescribeRole.Theorem),
            Node("minimal_rewiring_forward", "minimal rewiring forward", "Exact declaration: theorem minimal_rewiring_forward {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) (hminimal : Minimal original selection) : Minimal modified selection.", DescribeRole.Theorem),
            Node("minimal_rewiring", "minimal rewiring", "Exact declaration: theorem minimal_rewiring {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) : Minimal original selection ↔ Minimal modified selection.", DescribeRole.Theorem),
            Node("fanoNeighbors", "fanoNeighbors", "Exact declaration: def fanoNeighbors (vertex : Fin 14) : List (Fin 14).", DescribeRole.Definition),
            Node("FanoAdj", "FanoAdj", "Exact declaration: def FanoAdj (first second : Fin 14) : Prop.", DescribeRole.Definition),
            Node("fanoSelected", "fanoSelected", "Exact declaration: def fanoSelected (vertex : Fin 14) : Prop.", DescribeRole.Definition),
            Node("fanoFailure", "fanoFailure", "Exact declaration: def fanoFailure (vertex : Fin 14) : Fin 14.", DescribeRole.Definition),
            Node("fano_simple_cubic", "fano simple cubic", "Exact declaration: theorem fano_simple_cubic : (∀ vertex : Fin 14, ¬ FanoAdj vertex vertex) ∧ (∀ first second : Fin 14, FanoAdj first second ↔ FanoAdj second first) ∧ (∀ vertex : Fin 14, (fanoNeighbors vertex).length = 3 ∧ (fanoNeighbors vertex).Nodup).", DescribeRole.Theorem),
            Node("fano_forms", "fano forms", "Exact declaration: theorem fano_forms : Forms FanoAdj fanoSelected.", DescribeRole.Theorem),
            Node("fano_deletion_failures", "fano deletion failures", "Exact declaration: theorem fano_deletion_failures : ∀ deleted : Fin 14, fanoSelected deleted → ¬ (fanoSelected (fanoFailure deleted) ∧ fanoFailure deleted ≠ deleted) ∧ ¬ TwoAt FanoAdj (fun vertex => fanoSelected vertex ∧ vertex ≠ deleted) (fanoFailure deleted).", DescribeRole.Theorem),
            Node("fano_minimal", "fano minimal", "Exact declaration: theorem fano_minimal : Minimal FanoAdj fanoSelected.", DescribeRole.Theorem),
            Node("fano_selected_card", "fano selected card", "Exact declaration: theorem fano_selected_card : ((List.finRange 14).filter (fun vertex => decide (fanoSelected vertex))).length = 8.", DescribeRole.Theorem)), []));
}
