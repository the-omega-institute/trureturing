using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CoverDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CoverDensity.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual certificate density in uniform finite covers", H("Actual certificate density in uniform finite covers"),
        Blocks(Paragraph(Text("Neighborhood bijections preserve finite vertex degrees and pull back a two-coloring. Uniform fibers give the complete whole-order identity, including zero fibers and empty bases. Every actual base dissociation set yields its stated density in the lift. For cubic bipartite bases this combines with sharp compensation to bound the actual canonical gap. Above either supplied S/J two-lift the density is at least four sevenths and gap at most one forty-ninth of the order. No arbitrary even nonregular cover factorization or higher-cover SF exactness is assumed.")),
            Node("degree_cover", "degree cover", "Exact declaration: theorem degree_cover (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (v : W) : DegreeCapacity.degree H v = DegreeCapacity.degree G (p v).", DescribeRole.Theorem),
            Node("colorable_cover", "colorable cover", "Exact declaration: theorem colorable_cover (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (hG : G.Colorable 2) : H.Colorable 2.", DescribeRole.Theorem),
            Node("card_cover", "card cover", "Exact declaration: theorem card_cover (p : W → V) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : Fintype.card W = k * Fintype.card V.", DescribeRole.Theorem),
            Node("certificate_density", "certificate density", "Exact declaration: theorem certificate_density (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (A : Finset V) (hA : IsKIndependent G 2 A) : A.card * Fintype.card W ≤ Fintype.card V * beta H 2.", DescribeRole.Theorem),
            Node("cubic_certificate_gap", "cubic certificate gap", "Exact declaration: theorem cubic_certificate_gap (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (hG : G.Colorable 2) (hr : ∀ v, DegreeCapacity.degree G v = 3) (A : Finset V) (hA : IsKIndependent G 2 A) : (7 * Fintype.card V) * (SF H 2 - beta H 2) ≤ (3 * Fintype.card V - 5 * A.card) * Fintype.card W.", DescribeRole.Theorem),
            Node("scalar_cover_bound", "scalar cover bound", "Exact declaration: theorem scalar_cover_bound {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28) (cover : CoverPullback.NeighborhoodCover HeawoodCertificates.scalarGraph.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : 4 * Fintype.card U ≤ 7 * beta H 2 ∧ 49 * (SF H 2 - beta H 2) ≤ Fintype.card U.", DescribeRole.Theorem),
            Node("jordan_cover_bound", "jordan cover bound", "Exact declaration: theorem jordan_cover_bound {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28) (cover : CoverPullback.NeighborhoodCover HeawoodCertificates.jordanGraph.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : 4 * Fintype.card U ≤ 7 * beta H 2 ∧ 49 * (SF H 2 - beta H 2) ≤ Fintype.card U.", DescribeRole.Theorem)), []));
}
