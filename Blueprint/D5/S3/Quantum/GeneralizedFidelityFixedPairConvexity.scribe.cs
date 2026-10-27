using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class GeneralizedFidelityFixedPairConvexityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/GeneralizedFidelityFixedPairConvexity.";
    private static Formula P => F.Id("P");
    private static Formula Q => F.Id("Q");
    private static Formula R => F.Id("R");
    private static Formula Root(Formula a) => Call("sqrt", a);
    private static Formula Inverse(Formula a) => Seq(a, Caret, Grp(Minus, D(1)));
    private static Formula Product(params Formula[] a) => Seq(a);
    private static Formula Trace(Formula a) => Call("tr", a);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a fixed positive definite qubit reference R and a second input Q of trace one, "
        + "the squared generalized Bures--Wasserstein quantity is convex in its first "
        + "density-state input exactly when its Hermitian square-root coefficient is positive semidefinite.",
        H("Fixed-Pair Convexity of Generalized Fidelity"),
        Blocks(
            Node("densitySet", "The full qubit density domain",
                Equal(F.Id("densitySet"), Seq(OpenBrace, P, Sp, Bar, Sp,
                    Call("PSD", P), Sp, Land, Sp, Equal(Trace(P), D(1)), CloseBrace)),
                "The domain consists of all complex two by two positive semidefinite matrices "
                + "of trace one. It includes every rank-one boundary state and is convex over the real numbers.",
                DescribeRole.Definition),
            Node("coefficient", "The Hermitian trace coefficient",
                Equal(Call("coefficient", R, Q), Seq(Frac, Grp(D(1)), Grp(D(2)), Open,
                    Product(Inverse(R), Root(Product(Root(R), Q, Root(R)))), Plus,
                    Product(Root(Product(Root(R), Q, Root(R))), Inverse(R)), Close)),
                "Write S=sqrt(R), D=sqrt(SQS), and C=(R inverse D+D R inverse)/2. "
                + "When R is positive definite, C is Hermitian. Cyclicity of trace and conjugation give "
                + "Re fidelity(R,P,Q)=Re tr(C sqrt(SPS)). Every root uses the existing total "
                + "CFC.sqrt operation. On positive semidefinite arguments this is the positive "
                + "semidefinite square root; all root arguments are positive semidefinite in "
                + "the density-state specialization. The inverse is the actual matrix inverse.",
                DescribeRole.Definition),
            Node("fixed_pair_convexity_iff", "The exact positivity criterion",
                Disp(Seq(Forall, Sp, Q, Comma, R, Comma, Esc,
                    Equal(Trace(Q), D(1)), Sp, Land, Sp, Call("PD", R), Sp, Rightarrow, Sp,
                    Open, Call("ConvexOn", F.Id("real"), F.Id("densitySet"),
                        Grp(LambdaLower, Sp, P, Comma, Call("bures", R, P, Q))), Sp, Iff, Sp,
                    Call("PSD", Call("coefficient", R, Q)), Close)),
                "For every complex two by two Q of trace one and positive-definite R, "
                + "convexity of P mapped to bures(R,P,Q) on the entire density domain is "
                + "equivalent to C being positive semidefinite. In particular, this applies when "
                + "Q is a density state, including singular Q, and R has trace one. "
                + "The original real trace term tr(P+Q) becomes two on this domain, so convexity "
                + "is equivalent to concavity of Re fidelity in P. If C is positive semidefinite, "
                + "the positive trace functional preserves the operator-concavity inequality for square root. "
                + "For necessity, diagonalize C=U diag(lambda0,lambda1) U star, set V=S inverse U, "
                + "alpha=Re (V star V)00 and beta=Re (V star V)11, and use the actual density matrices "
                + "P(t)=V diag((1-t)/alpha,t/beta) V star for 0<=t<=1. Both normalization "
                + "constants are strictly positive. The sandwiched matrices have eigenvalues "
                + "(1-t)/alpha and t/beta, so their actual roots give "
                + "Re fidelity=lambda0 sqrt(1-t)/sqrt(alpha)+lambda1 sqrt(t)/sqrt(beta). "
                + "Concavity places this function above its endpoint chord. Substituting t=x squared "
                + "and letting x decrease to zero forces lambda1>=0; reversing t forces lambda0>=0. "
                + "This is convexity in P for a fixed pair Q,R and does not assert joint convexity "
                + "or a data-processing property of channels.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("generalized-fidelity-fixed-pair-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
