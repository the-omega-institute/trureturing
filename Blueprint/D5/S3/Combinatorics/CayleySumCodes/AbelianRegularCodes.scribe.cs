using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class AbelianRegularCodesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes");
    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full finite abelian regular-code criteria on actual loopless sum graphs.",
        H("Regular perfect and total perfect subgroup codes"),
        Blocks(
            Item("ambient-square-subgroup", "squareSubgroup", "The subgroup of squares",
                "In an abelian group the squaring homomorphism has subgroup image. "
                + "This is the actual set of ambient squares, with no square premise "
                + "imposed on a witness subgroup.", DescribeRole.Definition),
            Item("square-subgroup-carrier", "squares_eq", "The exact square-set carrier",
                "The carrier of the squaring image equals the elementwise square set. "
                + "The finite Sylow/Frattini identity Sq(G)=Phi(Q)K below gives "
                + "the source correspondence with an actual odd Hall complement.", DescribeRole.Theorem),
            Item("square-free-transversal", "square_free_normalized",
                "A normalized transversal avoiding all nonidentity squares",
                "If H contains an ambient nonsquare z, modify each nonidentity "
                + "square representative t to tz, leaving 1 fixed. Every representative "
                + "stays in its original H-coset, uniqueness is preserved, and all "
                + "nonidentity representatives are ambient nonsquares. This is a "
                + "construction for all cosets, not a supplied transversal premise.", DescribeRole.Theorem),
            Item("regular-perfect-criterion", "perfect_iff", "The full regular PC criterion",
                "For every subgroup H of every finite abelian G, a regular sum graph "
                + "with H perfect exists exactly when H is trivial, H contains an "
                + "ambient nonsquare, or H equals Sq(G). The trivial subgroup is "
                + "perfect in CS(G,G), the complete simple graph. Omitting that "
                + "alternative would misstate the retained nontrivial-H antecedent "
                + "Zhang 5.3. Witness graphs may change during normalization.", DescribeRole.Theorem),
            Item("regular-total-criterion", "total_iff", "The corrected regular TPC criterion",
                "A subgroup H of a finite abelian G has a regular total-code witness "
                + "exactly when H contains an ambient nonsquare or Sq(G) has two "
                + "elements and lies in H. In the latter necessity branch H=Sq(G) "
                + "and |H|=2. Sufficiency constructs an actual square-free transversal "
                + "or inserts the two ambient squares into a normalized transversal. "
                + "This is the universal Proposition 3.2 argument; reported finite "
                + "tables do not prove this criterion.", DescribeRole.Theorem),
            Item("sylow-frattini-hall", "square_frattini_hall",
                "The exact square subgroup in Sylow and Hall coordinates",
                "For every finite abelian group and every actual Sylow-2 subgroup Q, "
                + "construct an actual complementary subgroup K of odd order and prove "
                + "Sq(G)=Phi(Q)K inside G. This discharges the separate identity in "
                + "Zhang 5.3 without assuming a decomposition or the desired square "
                + "identity. The scoped Frattini proof adapts Qiuzhen-CFSG/CFSG at "
                + "0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7, retaining its Apache-2.0 "
                + "source and license; actual Schur-Zassenhaus and finite-group "
                + "primitives are directly imported from the pinned Mathlib.", DescribeRole.Theorem),
            Item("even-abelian-nonsquare", "even_nonsquare", "An actual nonsquare",
                "Cauchy's theorem gives a nontrivial kernel element of the finite "
                + "squaring map; noninjectivity implies nonsurjectivity and hence a "
                + "nonsquare. The consumer is the total-code construction for even H.", DescribeRole.Theorem),
            Item("even-subgroup-total-code", "even_total_exists",
                "Every even abelian subgroup has a total-code witness",
                "For every even-order H in a finite abelian G, an actual H-nonsquare "
                + "and an abelian perfect-code transversal give total perfect coding "
                + "through the surviving singleton sufficiency. The nonsquare need "
                + "not be an ambient nonsquare, and no regularity conclusion follows. "
                + "This retains Zhang 5.4, separately from the corrected regular "
                + "criterion and all missing enumeration provenance.", DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/Regularity")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/NormalSubgroupCriterion"))]));
}
