using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class UniformCoefficientBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Interpolation/UniformCoefficientBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same exact interpolating polynomial separates two actual atomic supports without paying an inverse node-spacing cost.",
        H("Uniform coefficient budgets and joint Laplace certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-coeffl1"),
                DeclarationHandle.Create(Prefix + "coeffL1"),
                H("The monomial coefficient one-norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/tan2026coefficientonenorm")),
                Blocks(Paragraph(Text("For every real polynomial p, coeffL1(p) is the sum of |p.coeff k| over its finite support. The leaf definition and elementary norm proofs follow the licensed Causalean source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-coeffl1-add-le"),
                DeclarationHandle.Create(Prefix + "coeffL1_add_le"),
                H("The triangle inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/tan2026coefficientonenorm")),
                Blocks(Paragraph(Text("For every pair of real polynomials p and q, coeffL1(p+q) <= coeffL1(p)+coeffL1(q)."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-coeffl1-mul-le"),
                DeclarationHandle.Create(Prefix + "coeffL1_mul_le"),
                H("Submultiplicativity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/tan2026coefficientonenorm")),
                Blocks(Paragraph(Text("For every pair of real polynomials p and q, coeffL1(p*q) <= coeffL1(p)*coeffL1(q)."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-coeffl1-c-mul"),
                DeclarationHandle.Create(Prefix + "coeffL1_C_mul"),
                H("Scalar homogeneity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/tan2026coefficientonenorm")),
                Blocks(Paragraph(Text("For every real c and real polynomial p, coeffL1(C(c)*p)=|c| coeffL1(p)."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-coeffl1-x-sub-c"),
                DeclarationHandle.Create(Prefix + "coeffL1_X_sub_C"),
                H("A single nodal factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/tan2026coefficientonenorm")),
                Blocks(Paragraph(Text("For every real x, coeffL1(X-C(x))=1+|x|."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-interpolate-coeffl1-le"),
                DeclarationHandle.Create(Prefix + "interpolate_coeffL1_le"),
                H("Derivative budgets control the exact interpolant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/deboor2005divideddifferences")),
                Blocks(Paragraph(Text("Let s be any finite set of distinct real nodes in [a,b], with |x| <= 1 at every node. Let f have card(s)-1 continuous derivatives near every point of [a,b]. Suppose B(j) >= 0 for j < card(s), and |D^j f(x)| <= j! B(j) for every such j and every x in [a,b]. Then coeffL1(Lagrange.interpolate s id f) <= sum_{j<card(s)} 2^j B(j). Empty sets are allowed. Successive Rolle zeros identify each top coefficient with a derivative divided by a factorial. The Newton insertion identity and the nodal product budget propagate this estimate for the same exact interpolant. No positive separation between nodes is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-atomic-endpoint-certificate"),
                DeclarationHandle.Create(Prefix + "atomic_endpoint_certificate"),
                H("A common polynomial separates two atomic laws"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/deboor2005divideddifferences")),
                Blocks(Paragraph(Text("Let alpha and beta be nonnegative finitely supported real weights, beta have total mass 1, eta > 0, b < y <= 1, supp(alpha) be contained in [0,y], supp(beta) in [0,b], and alpha(y) >= eta. There exists a real polynomial P of degree strictly below N=card(supp(alpha) union supp(beta)), with sum alpha(x)P(x)-sum beta(x)P(x) >= 1 and coeffL1(P) <= (2/eta) sum_{j<N} [16/(eta(y-b))]^j/(2j)!. Here P=C(2/eta)*I, where I interpolates x -> endpoint(eta,(y-x)/(y-b)) on the union of both supports; coincident atoms have combined weight. Alpha need not have total mass 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-sparse-endpoint-coefficient-certificate"),
                DeclarationHandle.Create(Prefix + "sparse_endpoint_coefficient_certificate"),
                H("A finite-degree certificate budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the preceding atomic hypotheses, for every q > 0 with N <= q+1, there is a degree-at-most-q separating polynomial with coefficient budget (2/eta) [exp(1) max(1,16/(eta(y-b)q^2))]^q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-atomiclaplace"),
                DeclarationHandle.Create(Prefix + "atomicLaplace"),
                H("The Laplace curve of finite weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finitely supported real weight function mu and every real t, atomicLaplace(mu,t)=sum_E mu(E) exp(-t E). The definition imposes no positivity or normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-sparse-laplace-grid-certificate"),
                DeclarationHandle.Create(Prefix + "sparse_laplace_grid_certificate"),
                H("An exponential sampling grid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative finite weights mu and nu, total nu mass 1, eta > 0, h > 0, 0 <= gmu < gnu, support energies at least their corresponding grounds, mu(gmu) >= eta, and card(supp(mu))+card(supp(nu)) <= q+1 with q > 0, a linear combination of differences at times kh, k <= q, is at least 1. Its coefficient one-norm is at most (2/eta) [exp(1) max(1,16/(eta[exp(-h gmu)-exp(-h gnu)]q^2))]^q. The exponential map is injective and preserves the combined atomic weights."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-sparse-laplace-window-certificate"),
                DeclarationHandle.Create(Prefix + "sparse_laplace_window_certificate"),
                H("Legal times with a square-order gain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume E > 0, U > 0, 0 < eta <= 1, 0 <= gmu < gnu <= E, nonnegative weights with total nu mass 1 and ground mu mass at least eta. Both supports have at most m > 0 nodes and lie above their respective grounds. If m <= ceil(3/sqrt(eta Delta)), where Delta=(gnu-gmu)/E, put q=2m-1, M=max(1,q/U), h=1/(ME). There is a separating linear combination at times kh in [0,U/E], k <= q, with coefficient one-norm at most [288M/(eta^2 m^2 Delta)]^q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-ordered-laplace-joint-certificate"),
                DeclarationHandle.Create(Prefix + "ordered_laplace_joint_certificate"),
                H("The sparse and dense branches share one order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two nonnegative normalized finite weight laws on [gmu,E] and [gnu,E], with 0 <= gmu < gnu <= E, 0 < eta <= 1, ground mu mass at least eta, and at most d > 0 nodes each, every U > 0 admits the following certificate. Put Delta=(gnu-gmu)/E, m=min(d,ceil(3/sqrt(eta Delta))), q=2m-1, M=max(1,q/U), h=1/(ME). Then 0 < m <= d and m^2 Delta <= 16/eta; a separating combination at legal times kh in [0,U/E] has coefficient one-norm at most [1024M/(eta^2 m^2 Delta)]^q. The dense branch directly uses the Chebyshev noisy-moment endpoint estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interpolation-uniformcoefficientbudget-laplace-joint-certificates"),
                DeclarationHandle.Create(Prefix + "laplace_joint_certificates"),
                H("One order gives all-time and every window certificates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let E > 0, 0 < eta <= 1 and d > 0. Let mu and nu be nonnegative normalized finite weights with at most d nodes each, grounds gmu and gnu in [0,E], supports in [gmu,E] and [gnu,E], masses at both grounds at least eta, and distinct grounds. Put Delta=|gmu-gnu|/E, m=min(d,ceil(3/sqrt(eta Delta))) and q=2m-1. Then 0 < m <= d and m^2 Delta <= 16/eta. A separating combination at times k/E, k <= q, has coefficient one-norm <= [1024/(eta^2 m^2 Delta)]^q. For every U > 0, with M=max(1,q/U), another combination at times k/(ME) in [0,U/E] has coefficient one-norm <= [1024M/(eta^2 m^2 Delta)]^q. The same order m is used in both conclusions; the coefficient vectors may differ. No support-spacing or lower mass bound at nonground atoms is required."))),
                DescribeRole.Theorem))));
}
