using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13EnumerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Enumeration.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");
    private static readonly LibraryNoteRef Lagrange =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/gessel2016lagrange");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit formal series enumerates the original P13 avoiding perfect matchings at every natural size.",
        H("All-size enumeration of matchings avoiding 132, 213 and 321"),
        Blocks(
            Paragraph(Text("This unit concerns the P13 clause of Section 6, Question 1 in Biswas, Shankar and Sivasubramanian, arXiv:2609.08562v1. The carrier is the existing subtype of fixed-point-free involutions on Fin(2n) avoiding every pattern in P13 = {132, 213, 321}. An occurrence requires the three left endpoints to precede all three right endpoints; pattern labels follow the complementary right-endpoint convention. Empty and disconnected matchings are included. The P1 clause is outside this unit.")),
            Paragraph(Text("Write a_n for the natural cardinality of that subtype and A_0(X) = Σ a_n Xⁿ for actualSeries. All identities below hold in ℚ⟦X⟧. Put δ = (1 − X)², P = Φ₁, R = Φ₂, D = δ(1 − 2X − X²)P − X³(1 + X)R, and G = 1 + X(1 − X)³PD⁻¹. The inverse is the formal unit inverse of D, whose constant coefficient is one.")),
            Paragraph(Text("The scalar supplier defines Φ_j independently of matching counts: its coefficient at degree n is the finite sum, for 0 ≤ k ≤ n, of the coefficients of c_k (X^(j+1)δ⁻¹)^k. Here c_k = (−1)^k X^(k.choose 2) Σ_{r=0}^k DenInv(r)DenInv(k−r), and DenInv(r) is the unit inverse of ∏_{i=1}^r (1 − Xⁱ). This specifies the coefficient formula without a recurrence definition of a_n.")),
            Node("p13-enumeration-actual-a-eq-g", "The actual transformed series equals G", "actual_A_eq_G",
                "The actual H supplier defines h_k as the kth polynomial-coefficient row of its transformed literal completion series. Its three boundary laws and its proved Bulk recurrence supply every premise of the private boundary elimination. The t² law contains X(1−X)h₀. The actual minimal-solution identity at j=2 and the explicit Φ difference at j=1 give the remaining two equations. They imply (A−1)D = X(1−X)³P. Comparing with G_cleared and cancelling the unit D proves A=G. The proof never divides by X, h₀ or h₁, and assumes no equality with G.", AssessedProvenance.FromRepo(Source)),
            Node("p13-enumeration-actualseries-subst-zeta", "Lawful change of variable on the actual carrier", "actualSeries_subst_zeta_eq_G",
                "The original counting series satisfies A_0.subst ζ = G, where ζ = X(1+X)⁻². The proof identifies the H supplier’s Z with the Catalan supplier’s ζ using their square-unit identities, then uses Mathlib’s subst_eq_eval₂ under the discrete coefficient topology to identify the actual eval₂ series. The catalytic marker remains polynomial coefficient evaluation, not substitution of a nonzero-constant outer series.", AssessedProvenance.FromRepo(Source)),
            Node("p13-enumeration-actualseries-eq-g-subst-q", "Recovering the original counting series", "actualSeries_eq_G_subst_q",
                "Let q be the rational image of Mathlib’s Catalan series minus one. Then A_0 = G.subst q. Both ζ and q have zero constant coefficient, so HasSubst is proved for each. Mathlib’s lawful substitution associativity and the retained inverse identity ζ.subst q = X recover the original series. The unused reverse inverse is omitted from this delivery.", AssessedProvenance.FromRepo(Lagrange)),
            Node("p13-enumeration-result", "The unconditional cardinality coefficient formula", "result",
                "The empty matching count is a₀=1. For every natural n≥1, the rational cast of the original cardinality a_n is coeff n ((1−X)(1+X)^(2n−1)G). The arbitrary-series Catalan/Lagrange transform applies to the explicit G after recovery of A_0. There is no Bulk, H, recurrence, height bound, finite-n restriction, or equality-to-G hypothesis in the final statement. This is a formal P13 enumeration proof; it does not assert official acceptance, unique credit, worldwide novelty, or resolution of all of Question 1.", AssessedProvenance.FromRepo(Source))
        ),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/PatternMatchings/P13HCoefficients")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/PatternMatchings/P13Scalar")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge"))
        ]));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
