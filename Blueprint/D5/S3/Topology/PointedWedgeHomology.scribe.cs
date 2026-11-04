using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class PointedWedgeHomologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/PointedWedgeHomology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Based open contractions yield the actual singular homology of a binary quotient wedge.",
        H("Open saturated subwedges and singular homology"),
        Blocks(
            Node("part", "part", "A saturated subwedge",
                "Given pointed topological spaces (X,a),(Y,b), and subsets A,B containing their respective basepoints, part is the subset of the literal FiniteConeUnionWedge.Wedge quotient represented by A sum B. Membership descends because the complete pair of identified basepoints lies in those pieces.", DescribeRole.Definition),
            Node("open", "isOpen_part", "Open pieces give an open saturated subwedge",
                "If A and B are open, their saturated part is open in the actual quotient topology. The proof uses the quotient-map characterization of open subsets and the disjoint-sum topology.", DescribeRole.Theorem),
            Node("homeomorph", "partHomeomorph", "The subspace is the quotient wedge of the pieces",
                "For open A,B containing a,b, the wedge of the subtype basepoints in A and B is homeomorphic to part. The raw subtype-sum homeomorphism, the restricted open quotient map and equality of the complete quotient kernels construct this homeomorphism. All equal, distinct and cross-summand representatives are included.", DescribeRole.Definition),
            Node("left", "leftEquiv", "Collapsing a based contractible right summand",
                "An actual homotopy of the identity on Y to the constant b map, relative to b, gives Wedge(a,b) homotopy equivalent to X. The maps are the left projection and left inclusion. Their inverse homotopy reuses the genuine private FiniteConeUnionWedge.wedgeInverseHomotopy and wedgeMap through Batteries.OpenPrivate. That supplier descends the cylinder homotopy continuously by continuous_lift_prod_right and local compactness of the unit interval; no unproved quotient-cylinder continuity premise is added.", DescribeRole.Definition),
            Node("right", "rightEquiv", "Collapsing a based contractible left summand",
                "The actual quotient-swap homeomorphism followed by leftEquiv gives equivalence to Y whenever the contraction of X fixes a.", DescribeRole.Definition),
            Node("contractible", "contractible_wedge", "Two based contractions contract the quotient wedge",
                "If both summands have identity-to-basepoint homotopies fixing their basepoints, the actual wedge is contractible. The proof transports the contraction through leftEquiv and is used for the intersection of the open cover.", DescribeRole.Theorem),
            Node("homology", "homologyIso", "Positive-degree homology of the actual quotient wedge",
                "Suppose a and b have open neighborhoods A and B with the supplied contractions relative to those basepoints. For every q>0 and coefficient object in an abelian category with the required coproducts, H_q(X;R) biproduct H_q(Y;R) is isomorphic to H_q(Wedge(a,b);R). The saturated open subsets X wedge B and A wedge Y cover the quotient. They are homotopy equivalent to X and Y, and their intersection is homeomorphic to A wedge B and contractible. OpenCoverHomology.inclusionIso supplies the actual open Mayer–Vietoris split, including the reduced-H_0 argument for q=1. Positive reduced and ordinary homology are definitionally equal in the existing TauCeti port. The open-cover method is classical; these source-bound quotient and homotopy constructions are local implementation content.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
