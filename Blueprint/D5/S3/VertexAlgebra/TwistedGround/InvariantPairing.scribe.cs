using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class InvariantPairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/InvariantPairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite average constructs a nondegenerate complex bilinear form on the selected actual twisted ground, with the original signed charge adjointness.",
        H("An Invariant Bilinear Form on the Actual Twisted Ground"),
        Blocks(
            Paragraph(Text("Let D be a finite-rank even integral lattice with symmetric Gram matrix G and integer unit determinant. "
                + "Let T=ActualGround(D,hu) and rho be the representation selected by the actual finite ground existence theorem. "
                + "The carrier is the finite function space Half(groundRank(D,hu)) to C. The original reflection quotient H=E/K "
                + "is identified with its sign and mod-two charge coordinates. Its order is 2 times 2^rank(D). "
                + "No change of the selected representation, positivity, rank-24 condition or rootlessness is assumed.")),
            Describe.Lean(
                DescribeId.Create("actual-ground-pairing"),
                DeclarationHandle.Create(Prefix + "actual_ground_pairing"),
                H("Finite averaging, nondegeneracy and signed charge adjointness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On the complex vector space of bilinear forms define the contragredient action "
                        + "g.B(u,v)=B(rho(g inverse)u,rho(g inverse)v), and let P be its finite group average. "
                        + "Mathlib's Representation.averageMap and averageMap_invariant supply this average and its invariance. "
                        + "The character of this action is the square of tr(rho(g inverse)), by the existing dual and Hom character formulas. "
                        + "The selected actual trace vanishes at every nonzero mod-two charge. At the two central elements it is d and -d, "
                        + "where d=dim_C(T)=2^(rank(D)/2). Hence the sum of the squared characters is 2d^2, and tr(P)=2d^2/|H|=1.")),
                    Paragraph(Text("Consequently P is nonzero. In the coordinate bilinear basis E_(s,t)(u,v)=u(t)v(s), "
                        + "some E_(s,t) has nonzero average B=P(E_(s,t)). This constructs B on the selected actual T, "
                        + "rather than selecting a new Weyl representation or assuming an invariant form. "
                        + "The left radical of B is a subrepresentation: invariance moves rho(g) from a radical vector "
                        + "to rho(g inverse) on the other argument. The existing irreducibility makes this radical zero or all of T; "
                        + "nonzeroness excludes the latter. Finite-dimensional bilinear duality gives both nondegeneracy directions.")),
                    Paragraph(Text("For an integral charge alpha write R_alpha=rho([(0,alpha)]). The original square law is "
                        + "R_alpha^2=(-1)^(G(alpha,alpha)/2) identity. Applying invariance to (u,R_alpha v) and using this square law gives "
                        + "B(R_alpha u,v)=(-1)^(G(alpha,alpha)/2) B(u,R_alpha v). The same charge occurs on both sides. "
                        + "This is a bilinear adjointness law and does not replace transpose by Hermitian conjugation; "
                        + "the actual matrices may contain fourth-root phases.")),
                    Paragraph(Text("The construction includes rank zero, where the sole ground coordinate is the empty function "
                        + "and the quotient still has its two signs. The theorem asserts no symmetry of B. "
                        + "To obtain a symmetric form by symmetrizing the average, one still needs the positive quadratic Gauss sign "
                        + "sum_a (-1)^q(a)=2^(rank(D)/2) from integer even unimodularity. That arithmetic assertion, "
                        + "the oscillator Wick extension, all-source opposite covariance and the two-twisted-input intertwiner "
                        + "are separate mathematical obligations. No VOA extension, fusion rule, Monster action, string construction "
                        + "or AdS/CFT bridge follows from the finite pairing alone."))),
                DescribeRole.Theorem))));
}
