using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryPolarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let G be the original real biased boundary L2 space, let G0 be its mean-zero subspace, and let K be the orthogonal complement of the original edge covariance kernel. The paired Hilbert bases identify K and G0 by the real linear isometry equivalence W that preserves every coefficient. No scalar extension is used.",
        H("The Actual Real Polar Realization"), Blocks(
            Describe.Lean(DescribeId.Create("biasedboundarypolar-theorem"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.actual_polar_domains_resolvent"),
                H("The Actual Real Polar Realization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let G be the original real biased boundary L2 space, let G0 be its mean-zero subspace, and let K be the orthogonal complement of the original edge covariance kernel. The paired Hilbert bases identify K and G0 by the real linear isometry equivalence W that preserves every coefficient. No scalar extension is used.")),
                    Paragraph(Text("The bounded operator S is the centered trace on K transported back by W. The paired basis and the original adjoint show on every vector that S multiplies coefficient i by sqrt(mu(i)). The operator T is the original Sigma restricted to K and multiplies coefficient i by mu(i). Thus S squared equals T and the actual centered trace is W composed with S. Their strictly positive diagonal coefficients make both S and T injective, so their inverses on their respective ranges are unambiguous. On centered boundary vectors the original adjoint is S composed with W inverse, followed by the inclusion into the original edge space.")),
                    Paragraph(Text("A centered boundary vector belongs to the original free-root form domain exactly when it is W(S(x)) for some x in K. It belongs to the original operator domain exactly when it is W(T(x)). The original operator graph consists precisely of pairs (u,h) with h=W(x) and Pi(u)=W(T(x)), with each centered vector included into G. Hence the operator on G0 is the inverse of T transported by W; the inverse is used on the range of T. The analogous inverse of S is used on the range of S.")),
                    Paragraph(Text("The original least increment lift retains its root coefficient mean(F)-mean(J(lift(F))). The domain identification uses that original representation and its attained least energy; it does not identify the energy of an arbitrary extension with the minimum.")),
                    Paragraph(Text("The bounded operator R multiplies every K coefficient by 1/(1+mu(i)). Both R(x)+T(R(x))=x and R(x+T(x))=x hold on all of K. In contrast with the inverse of T, this inverse of I+T is total.")),
                    Paragraph(Text("For every F in G, the original resolvent equals constG(mean(F)) plus W(T(R(W inverse(Pi(F))))), included in G. This is the literal sum of the projection onto constants and W T (I+T) inverse W adjoint on the centered summand. The proof constructs a pair in the original weak graph whose sum is F and applies the already established inverse characterization of the resolvent. The original compact-resolvent and simple-zero-mode results therefore concern this same operator."))), DescribeRole.Theorem))));
}
