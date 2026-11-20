using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Foundations;

internal sealed class LocalFormationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local star formation on arbitrary graphs", H("Local star formation on arbitrary graphs"),
        Blocks(Paragraph(Text("The local witness predicate describes a non-induced two-leaf star containing each outside vertex. Inclusion-minimality is characterized by actual failures after single deletions. The graph, vertex type and selected set are arbitrary. These local proofs come from the original Amplification source in subquorum-colorings revision 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.")),
            Node("TwoAt", "TwoAt", "Exact declaration: def TwoAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop.", DescribeRole.Definition),
            Node("Forms", "Forms", "Exact declaration: def Forms {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop.", DescribeRole.Definition),
            Node("Minimal", "Minimal", "Exact declaration: def Minimal {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop.", DescribeRole.Definition),
            Node("LiteralAt", "LiteralAt", "Exact declaration: def LiteralAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop.", DescribeRole.Definition),
            Node("literal_iff_local", "literal iff local", "Exact declaration: theorem literal_iff_local {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) (hx : x ∉ S) : LiteralAt G S x ↔ TwoAt G S x.", DescribeRole.Theorem),
            Node("twoAt_mono", "twoAt mono", "Exact declaration: theorem twoAt_mono {V : Type*} (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) {x : V} : TwoAt G S x → TwoAt G T x.", DescribeRole.Theorem),
            Node("minimal_of_deletion_failures", "minimal of deletion failures", "Exact declaration: theorem minimal_of_deletion_failures {V : Type*} (G : SimpleGraph V) (S : Set V) (hforms : Forms G S) (hfail : ∀ selected ∈ S, ∃ x, x ∉ S \\ {selected} ∧ ¬ TwoAt G (S \\ {selected}) x) : Minimal G S.", DescribeRole.Theorem)), []));
}
