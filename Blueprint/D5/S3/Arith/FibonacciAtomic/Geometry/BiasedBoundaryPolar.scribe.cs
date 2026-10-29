using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryPolarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let G be the original real biased boundary L2 space, let G0 be its mean-zero subspace, and let K be the orthogonal complement of the original edge covariance kernel. The paired Hilbert bases identify K and G0 by the real linear isometry equivalence W that preserves every coefficient. No scalar extension is used.",
        H("The Actual Real Polar Realization"), Blocks(
            Describe.Lean(DescribeId.Create("biasedboundarypolar-polar"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.polar"),
                H("The Paired Basis Isometry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The real isometry from K to G0 is k.repr followed by the inverse of b.repr. It preserves all coefficients of the paired Hilbert bases."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("biasedboundarypolar-tracek"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.traceK"),
                H("The Centered Trace on Its Complete Input Support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("traceK is the original centered trace restricted to K and regarded in its specified mean-zero codomain G0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("biasedboundarypolar-tracecoeff"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.trace_coeff"),
                H("Paired Singular Coordinates of the Original Trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For the same complete paired bases b,k and strictly positive mu satisfying Sigma(k(i))=mu(i)k(i) and C(k(i))=sqrt(mu(i))b(i), the b coefficient of traceK(x) equals sqrt(mu(i)) times the k coefficient of x, for every x in K and every i. The identity follows from the actual adjoint and Gram relation, so the paired coefficients belong to the original real operator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarypolar-covariancek"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.covarianceK"),
                H("The Original Covariance on K"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("covarianceK is Sigma restricted to K and codomain-restricted to K using the adjoint range inclusion. Its coefficient formula relates the original covariance to the boundary graph."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("biasedboundarypolar-polarcoeff"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.polar_coeff"),
                H("Paired Isometry Coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every x in K and every index i, the b coefficient of polar(b,k)(x) equals the k coefficient of x."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarypolar-covariancecoeff"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.covariance_coeff"),
                H("Covariance Coefficients on the Same Family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For paired bases b,k and positive mu with the original Sigma and C basis actions, every x in K has covarianceK coefficient mu(i) times its k coefficient. The heat uses this formula on the same ordered spectral family as its eigenvalue bounds."))), DescribeRole.Theorem),
            Paragraph(Text("For the original global counting family, retain the same e,k,mu with K equal to the orthogonal complement of ker(Sigma), mu positive and antitone tending to zero, and b=phi to the power minus two and B=2 phi cubed. The counting bounds give b/(i+1) at most mu(i) at most B/(i+1). To apply SupportedSingular.approximationNumber_eq_supported to Sigma on the full edge carrier H, take A to be Sigma with codomain restricted to K, the output basis to be k, and the output isometry to be the actual inclusion K into H. The C_project identity and covariance_coeff give its required all-vector coefficients.")),
            Paragraph(Text("For centeredTrace:H to G0, take A=centeredTrace, input support K, input basis k, output basis e and the identity output isometry. The same C_project identity and trace_coeff give the coefficient sqrt(mu(i)) times the k coefficient of the projection onto K. For the ambient C:H to G, retain exactly this A,e,k,mu and use the actual isometric inclusion of G0 into G. The complete support basis and the paired original operator equations give the singular system; both centeredTrace* centeredTrace and C* C equal the same original Sigma. Thus all zero-based approximation numbers of Sigma equal mu(i), and those of centeredTrace and ambient C both equal sqrt(mu(i)), with the full edge kernel retained and all bounded finite rank competitors allowed.")),
            Paragraph(Text("The original operators are compact. For every real r greater than zero, the two-sided mu bounds and the real p-series criterion give summability of the actual Sigma singular values to the power r exactly when r is greater than one. The paired trace singular values give the threshold r greater than two, in either the centered or ambient codomain. At the endpoints, Sigma has summable squares but not summable first powers, while neither trace has summable squares. These are the Hilbert-Schmidt and trace class consequences for the original supported singular system. They require the complete support and actual Gram identities above; the scalar comparison alone supplies no operator ideal statement.")),
            Describe.Lean(DescribeId.Create("biasedboundarypolar-graphpolar"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.graph_polar"),
                H("The Parameterized Original Graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For the same paired bases and covariance actions, an arbitrary pair (u,h) of ambient boundary vectors belongs to boundaryOperator.graph exactly when some x in K has h=polar(x) and Pi(u)=polar(covarianceK(x)), with the original inclusions into G. This identity describes the entire graph and its domain."))), DescribeRole.Theorem),
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
