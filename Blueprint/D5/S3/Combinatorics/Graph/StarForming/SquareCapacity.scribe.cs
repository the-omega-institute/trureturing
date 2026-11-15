using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SquareCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform weighted square certificates", H("Uniform weighted square certificates"),
        Blocks(Paragraph(Text("A square has four distinct vertices and the four cyclic edges; diagonals are allowed. Every dissociation selection meets it in at most two vertices. Finite weighted incidence is counted exactly by interchanging the vertex and square sums. Nonnegative rational square weights with total incident capacity one at every vertex imply two beta two<=n. For a bipartite graph the color-class lower bound attains equality. No SF equality, strict gain in a connected cover, or preservation of a positive gap is inferred.")),
            Node("Square", "Square", "Exact declaration: structure Square (G : SimpleGraph V).", DescribeRole.Definition),
            Node("Square.carrier", "Square.carrier", "Exact declaration: def Square.carrier {G : SimpleGraph V} (C : Square G) : Finset V.", DescribeRole.Definition),
            Node("carrier_card", "carrier card", "Exact declaration: theorem carrier_card {G : SimpleGraph V} (C : Square G) : C.carrier.card = 4.", DescribeRole.Theorem),
            Node("intersection_cap", "intersection cap", "Exact declaration: theorem intersection_cap (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hS : IsKIndependent G 2 S) (C : Square G) : (S ∩ C.carrier).card ≤ 2.", DescribeRole.Theorem),
            Node("weighted_intersections", "weighted intersections", "Exact declaration: theorem weighted_intersections {Q : Type*} [Fintype Q] (C : Q → Finset V) (weight : Q → ℚ) (S : Finset V) : ∑ q : Q, weight q * ((S ∩ C q).card : ℚ) = ∑ v ∈ S, ∑ q : Q, if v ∈ C q then weight q else 0.", DescribeRole.Theorem),
            Node("uniform_intersections", "uniform intersections", "Exact declaration: theorem uniform_intersections {Q : Type*} [Fintype Q] (C : Q → Finset V) (weight : Q → ℚ) (huniform : ∀ v, (∑ q : Q, if v ∈ C q then weight q else 0) = 1) (S : Finset V) : ∑ q : Q, weight q * ((S ∩ C q).card : ℚ) = S.card.", DescribeRole.Theorem),
            Node("selection_bound", "selection bound", "Exact declaration: theorem selection_bound (G : SimpleGraph V) [DecidableRel G.Adj] {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ) (hweight : ∀ q, 0 ≤ weight q) (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1) (S : Finset V) (hS : IsKIndependent G 2 S) : 2 * S.card ≤ Fintype.card V.", DescribeRole.Theorem),
            Node("beta_bound", "beta bound", "Exact declaration: theorem beta_bound (G : SimpleGraph V) [DecidableRel G.Adj] {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ) (hweight : ∀ q, 0 ≤ weight q) (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1) : 2 * beta G 2 ≤ Fintype.card V.", DescribeRole.Theorem),
            Node("beta_exact", "beta exact", "Exact declaration: theorem beta_exact (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Colorable 2) {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ) (hweight : ∀ q, 0 ≤ weight q) (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1) : 2 * beta G 2 = Fintype.card V.", DescribeRole.Theorem)), []));
}
