using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class SingletonRetractionBasedInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/SingletonRetractionBasedInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual singleton-cylinder retractions produce both relative inverse homotopies.",
        H("A based inverse from an ordinary homotopy equivalence"),
        Blocks(
            Node("cylinder", "CylinderRetraction", "The actual retraction input",
                "For a topological space Z and point p, the supplied continuous map has codomain the subspace of Z times the unit interval consisting of the bottom and the cylinder over p. It fixes every point of that subspace. This is actual topological data, rather than an assumed homotopy extension property.", DescribeRole.Definition),
            Node("boundary", "SquareBoundary", "The relative-square boundary",
                "The subspace of Z times the square consists of the square's bottom and two vertical sides over every point of Z, together with the entire square over p.", DescribeRole.Definition),
            Node("square", "squareRetraction", "An explicit boundary retraction",
                "For q=(t,s), put d=max(1-s/2,abs(2t-1)), ell=1-d, and rho=(1/2,2)+(q-(1/2,2))/d. The denominator is at least one half. The point rho lies on the three prescribed sides, and q=d rho+(1-d)(1/2,2). If the supplied retraction at (z,ell) is (zhat,tau), set a=min(tau,ell). The output is (zhat,(1-a)rho+a(1/2,2)). Its square coordinate stays between rho and q; positive a forces zhat=p. The construction is continuous and fixes both boundary pieces. The based inverse proof consumes this retraction when straightening each null basepoint trace.", DescribeRole.Definition),
            Node("data", "BasedEquivalence", "Both relative identities",
                "The data consist of continuous maps F and G between the original spaces, the identities F(x)=y and G(y)=x, a homotopy from GF to the identity relative to {x}, and a homotopy from FG to the identity relative to {y}.", DescribeRole.Definition),
            Node("inverse", "based_inverse", "Constructing the based inverse",
                "Let X and Y be T1 spaces with selected points x and y and actual singleton-cylinder retractions. Given continuous f and g, ordinary homotopies gf to the identity and fg to the identity, and an explicit path gamma from f(x) to y, the theorem constructs a BasedEquivalence and a homotopy A from f to its forward map whose trace at x is exactly gamma. Closed pasting followed by the supplied retraction extends gamma to A. The trace beta of the updated left inverse homotopy extends g to the new G. Reversing this extension and then following the updated left homotopy gives trace beta(abs(2t-1)), contracted by beta(s+(1-s)abs(2t-1)). The square retraction straightens it relative to x, producing U for the new composite GF. For C=FG and an ordinary right inverse homotopy V, the proof concatenates reverse(V after C), FUG, and V. Native binary concatenation has stages of lengths one quarter, one quarter, and one half. Its trace is delta(max(max(1-4t,0),2t-1)), where delta is the trace of V; the middle trace is constant because U fixes x. The same affine contraction and square straightening give the relative right identity. No contractibility of the original delta is assumed. This is the classical one-point cofiber homotopy equivalence bridge (May, A Concise Course in Algebraic Topology, Chapter 6, section 5, pp. 46-48); it supplies a missing Lean construction for sphere-wedge transport and makes no claim to settle Carnero Question 22 or to mathematical novelty.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
