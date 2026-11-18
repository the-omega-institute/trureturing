using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Families;

internal sealed class HeawoodCoverDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cover density above the S and J two-lifts", H("Cover density above the S and J two-lifts"),
        Blocks(Paragraph(Text("The actual sixteen-vertex S and J dissociation selections are used by the generic certificate-density and cubic-gap theorems. Every uniform cover above either fixed two-lift has beta density at least four sevenths and SF-minus-beta density at most one forty-ninth. The cover, fiber cardinality and uniformity hypotheses remain explicit. No classification conclusion is added.")),
            Node("scalar_cover_bound", "scalar cover bound", "Exact declaration: theorem scalar_cover_bound {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28) (cover : CoverPullback.NeighborhoodCover HeawoodCertificates.scalarGraph.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : 4 * Fintype.card U ≤ 7 * beta H 2 ∧ 49 * (SF H 2 - beta H 2) ≤ Fintype.card U.", DescribeRole.Theorem),
            Node("jordan_cover_bound", "jordan cover bound", "Exact declaration: theorem jordan_cover_bound {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28) (cover : CoverPullback.NeighborhoodCover HeawoodCertificates.jordanGraph.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : 4 * Fintype.card U ≤ 7 * beta H 2 ∧ 49 * (SF H 2 - beta H 2) ≤ Fintype.card U.", DescribeRole.Theorem)), []));
}
