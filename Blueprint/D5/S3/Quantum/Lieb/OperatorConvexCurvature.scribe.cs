using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class OperatorConvexCurvatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Lieb/OperatorConvexCurvature.";
    private static Formula Fn => Seq(Real(), To, Real());
    private static Formula PositiveRay => Call("Ioi", D(0));
    private static Formula ScalarConvex => Call("ConvexOn", Real(), PositiveRay, Id("f"));
    private static Formula OperatorConvex => Call("OperatorConvexOnAll", PositiveRay, Id("f"));
    private static Formula MatrixConvex => Call("OperatorConvexOn", Call("ComplexTwoByTwoMatrices"), PositiveRay, Id("f"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonaffine operator-convex real function on the positive ray has full support of its actual right-derivative Stieltjes curvature.",
        H("Operator-convex affine rigidity and curvature"), Blocks(
            Paragraph(Text("All operator-convex predicates here are the existing domain-aware CFC predicates with domain Ioi 0. Their quantified inputs are actual selfadjoint operators with spectra in the positive ray. The matrix predicate uses complex two by two matrices with the existing Loewner order and actual real continuous functional calculus. OperatorConvexOnAll quantifies over all complex Hilbert spaces in Type 0. No continuous Jensen theorem, integral representation, strict convexity, curvature support, normalization or endpoint assumption is supplied as a premise.")),
            Node("affine_of_matrixConvex", All("f", Fn, Imp(ScalarConvex, Imp(MatrixConvex,
                All("a", Real(), All("b", Real(), All("alpha", Real(), All("gamma", Real(),
                    Imp(Lt(D(0), Id("a")), Imp(Lt(Id("a"), Id("b")),
                        Imp(OnAffine(Call("Ioo", Id("a"), Id("b"))), OnAffine(PositiveRay))))))))))),
                "A local affine formula propagates to every positive real. Subtracting that line gives a scalar convex nonnegative function g vanishing on an interval. Choose q and beta>0 with q-beta,q,q+beta in that interval. For A=diag(q,w), B=[[q,beta],[beta,q]], and 0<t<1, the matrices A, B and D=(1-t)A+tB have actual positive spectra. Convexity bounds 0<=g(D)<=(1-t)g(A), whose first diagonal entry is zero. The positive-semidefinite zero-quadratic-form theorem kills the first column of g(D). CFC commutation with D and the nonzero offdiagonal t*beta then kill the second column, so g(D)=0. For a target z!=q, set d=z-(t*beta)^2/(z-q) and w=(d-t*q)/(1-t). Ordinary scalar continuity at t=0 selects 0<t<1 with w>0. The exact two by two determinant proves z is in the real spectrum of D=[[q,t*beta],[t*beta,d]]. Injectivity of actual CFC on that spectrum gives g(z)=0. The case z=q was already zero. Every private matrix helper is consumed by this propagation proof."),
            Node("convexOn_of_operatorConvexOnAll", All("f", Fn,
                Imp(OperatorConvex, ScalarConvex)),
                "The existing all-Hilbert predicate is instantiated on the actual one-dimensional complex Euclidean Hilbert space. The star-algebra equivalence between one by one matrices and its bounded operators transports spectra, CFC and order. Applying the resulting inequality to scalar matrices gives scalar convexity. The same consumed transport is instantiated in dimension two for affine rigidity. This helper organizes existing CFC transport and the actual scalar inequality; it is consumed by the curvature theorem and is not claimed as new independent mathematical content."),
            Node("operatorConvex_curvature_full_support", All("f", Fn,
                All("hconv", OperatorConvex, Imp(Nonaffine(),
                    Eqn(Call("support", Call("curvature", Call("convexOnOfOperatorConvexOnAll", Id("hconv")))), Call("univPositive"))))),
                "Nonaffine means there do not exist real alpha and gamma with f(x)=alpha*x+gamma for every x>0. The scalar convexity proof in the curvature construction is derived from hconv, rather than assumed. The two-dimensional affine rigidity theorem supplies the complete premise of CurvatureAffineRigidity.full_support_of_affine_rigidity. A zero derivative increment would squeeze every secant slope on that interval to the same value and force a local affine formula, hence a global one. Nonaffineness therefore makes every right-derivative increment strictly positive. The actual curvature_Ioc identity gives positive mass on every positive half-open interval and hence on every neighborhood in Positive. The equality is support relative to Positive=(0,infinity), with no finiteness condition at zero or infinity."),
            Paragraph(Text("The finite spectral and convexity ingredients are classical. This is a necessary supplier for the Hiai–Mosonyi–Tomamichel setting, arXiv:2607.08760v1, whose maximal hockey-stick versus maximal f-divergence equality classification is a separate question. No world novelty or solution of that classification is asserted."))
        )));

    private static Formula OnAffine(Formula domain) => All("x", Real(),
        Imp(Call("mem", Id("x"), domain), Eqn(Call("f", Id("x")),
            Add(Mul(Id("alpha"), Id("x")), Id("gamma")))));
    private static Formula Nonaffine() => Seq(Neg, Sp, Exists, Sp, Id("alpha"), Sp, Id("gamma"),
        Sp, Colon, Real(), Comma, Sp, OnAffine(PositiveRay));
    private static DocumentBlock Node(string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("operator-convex-curvature-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
}
