using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HilbertGeometry;

internal sealed class HilbertSubspaceActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extended quadratic action on all absolutely continuous Hilbert paths with a closed-subspace initial constraint.",
        H("Hilbert Subspace Action"),
        Blocks(
            Paragraph(Text(
                "In all six statements, u and v are independent arbitrary universe levels; "
                + "Type with subscript u or v denotes Lean's Type u or Type v. Quantify "
                + "universally over K : Type u and H : Type v with RCLike K, "
                + "NormedAddCommGroup H, and InnerProductSpace K H. The definitions "
                + "quadraticAction and AdmissiblePath require only these classes; affinePath "
                + "and all three theorems also require CompleteSpace H. "
                + "Time, scalar multiplication along paths, and derivatives use the real scalar "
                + "structure obtained by restriction of scalars. Thus real and complex Hilbert "
                + "spaces are included, without separability or dimension assumptions. Where "
                + "used, M ranges over actual closed linear subspaces of H over K, x over H, "
                + "f over all paths from Real to H, and t over Real. Write P for M's "
                + "orthogonal starProjection, r = x - P x, and mu for Lebesgue measure restricted "
                + "to Ioc(0,1). The half-open and closed interval integrals coincide because "
                + "endpoints have measure zero. The notation S denotes quadraticAction, A "
                + "denotes AdmissiblePath, and g denotes affinePath(M,x).")),
            Describe.Lean(
                DescribeId.Create("hilbert-extended-quadratic-action"),
                DeclarationHandle.Create(Prefix + "quadraticAction"),
                H("Extended action"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("S", F.Id("f")), Sp, Eq, Sp, Seq(Frac, Grp(D(1)), Grp(D(2))), Sp,
                    Call("lintegral", Lambda("t", Call("ofReal", Sq(Call("norm",
                        Call("deriv", F.Id("f"), F.Id("t")))))), F.Id("mu"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every path f from Real to H, S(f) lies in ENNReal. The factor one-half "
                    + "and the integral are extended nonnegative real operations. Infinite "
                    + "quadratic action is permitted even when f is absolutely continuous."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hilbert-admissible-ac-path"),
                DeclarationHandle.Create(Prefix + "AdmissiblePath"),
                H("Admissible paths"),
                StatementSource.FromAuthor(Disp(Seq(
                    Admissible(F.Id("f")), Sp, Iff, Sp,
                    Call("AbsolutelyContinuousOnInterval", F.Id("f"), D(0), D(1)),
                    Sp, Land, Sp, Call("f", D(0)), Sp, InMacro, Sp, F.Id("M"),
                    Sp, Land, Sp, Call("f", D(1)), Sp, Eq, Sp, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The path class requires only absolute continuity on the interval and "
                    + "the stated endpoints. It does not assume finite action, squared-derivative "
                    + "integrability, or any regularity outside the interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hilbert-projection-affine-path"),
                DeclarationHandle.Create(Prefix + "affinePath"),
                H("Affine path"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("g", F.Id("t")), Sp, Eq, Sp, Call("P", F.Id("x")),
                    Sp, Plus, Sp, Call("smul", F.Id("t"), F.Id("r"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P is Mathlib's orthogonal projection onto M itself. This path is defined "
                    + "independently of the action and the minimizing property."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hilbert-finite-action-velocity-defect"),
                DeclarationHandle.Create(Prefix + "finite_action_velocity_defect"),
                H("Finite-action velocity defect"),
                StatementSource.FromAuthor(FiniteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here d = f(1) - f(0). The finite branch derives L2 membership of the "
                    + "totalized derivative and integrability of the squared velocity defect. "
                    + "The derivative is also proved to be the actual strong derivative almost "
                    + "everywhere. Endpoint reconstruction and the real inner-product norm "
                    + "expansion give the displayed exact variance identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hilbert-affine-path-attainment"),
                DeclarationHandle.Create(Prefix + "affine_path_attainment"),
                H("Affine attainment"),
                StatementSource.FromAuthor(WithContext(Seq(
                    Admissible(F.Id("g")), Sp, Land, Sp,
                    Call("S", F.Id("g")), Sp, Eq, Sp, Bound()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The affine path is absolutely continuous, starts at P x in M, ends at x, "
                    + "and has constant derivative r and exactly the stated finite action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hilbert-ac-subspace-action-minimum-unique"),
                DeclarationHandle.Create(Prefix + "absolutely_continuous_subspace_action_minimum_unique"),
                H("Minimum and pointwise uniqueness"),
                StatementSource.FromAuthor(MinimumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the full minimum over all admissible AC paths. The infinite-action "
                    + "case satisfies the lower bound and cannot attain the finite minimum. "
                    + "For finite action, orthogonal Pythagoras and the velocity-defect identity "
                    + "force f(0) = P x and derivative r almost everywhere when equality holds. "
                    + "The frozen Hilbert path fundamental theorem then reconstructs f(t) = g(t) "
                    + "at every t in Icc(0,1), including both endpoints. Conversely, equality "
                    + "of the paths on that interval gives the same action. Values outside "
                    + "the interval play no role."))),
                DescribeRole.Theorem))));

    private static Formula FiniteFormula()
    {
        Formula f = F.Id("f");
        Formula t = F.Id("t");
        Formula velocity = Call("deriv", f, t);
        Formula defect = Seq(velocity, Sp, Minus, Sp, F.Id("d"));
        Formula square = Lambda("t", Sq(Call("norm", velocity)));
        Formula squareDefect = Lambda("t", Sq(Call("norm", defect)));
        return WithSpace(Seq(
            Forall, Sp, f, Colon, Sp, F.Id("Real"), Sp, To, Sp, F.Id("H"), Comma, Sp,
            Call("AbsolutelyContinuousOnInterval", f, D(0), D(1)), Sp, Land, Sp,
            Call("S", f), Sp, Neq, Sp, Infty, Sp, Implies,
            RowBreak, Grp(),
            Call("MemLp", Call("deriv", f), D(2), F.Id("mu")), Sp, Land, Sp,
            Call("Integrable", squareDefect, F.Id("mu")), Sp, Land, Sp,
            Call("AlmostEverywhere", F.Id("mu"),
                Lambda("t", Call("HasDerivAt", f, velocity, t))), Sp, Land,
            RowBreak, Grp(),
            Call("integral", square, F.Id("mu")), Sp, Eq, Sp, Sq(Call("norm", F.Id("d"))),
            Sp, Plus, Sp, Call("integral", squareDefect, F.Id("mu"))));
    }

    private static Formula MinimumFormula() => WithContext(Seq(
        Admissible(F.Id("g")), Sp, Land, Sp, Call("S", F.Id("g")), Sp, Eq, Sp, Bound(),
        Sp, Land, RowBreak, Grp(),
        Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Real"), Sp, To, Sp, F.Id("H"), Comma, Sp,
        Admissible(F.Id("f")), Sp, Implies, Sp,
        Open, Bound(), Sp, Le, Sp, Call("S", F.Id("f")), Sp, Land,
        RowBreak, Grp(), Open,
        Call("S", F.Id("f")), Sp, Eq, Sp, Bound(), Sp, Iff, Sp,
        Call("EqOn", F.Id("f"), F.Id("g"), Call("Icc", D(0), D(1))),
        Close, Close));

    private static Formula WithContext(Formula conclusion) => WithSpace(Seq(
        Forall, Sp, F.Id("M"), Colon, Sp, Call("ClosedSubmodule", F.Id("K"), F.Id("H")),
        Comma, Sp, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("H"), Comma,
        RowBreak, Grp(), conclusion));

    private static Formula WithSpace(Formula conclusion) => Disp(Seq(
        Forall, Sp, F.Id("K"), Colon, Sp, Operatorname, Grp(F.Id("Type")), Underscore, Grp(F.Id("u")), Comma, Sp,
        Forall, Sp, F.Id("H"), Colon, Sp, Operatorname, Grp(F.Id("Type")), Underscore, Grp(F.Id("v")), Comma, Sp,
        OpenBracket, Call("RCLike", F.Id("K")), CloseBracket, Comma, Sp,
        OpenBracket, Call("NormedAddCommGroup", F.Id("H")), CloseBracket, Comma, Sp,
        OpenBracket, Call("InnerProductSpace", F.Id("K"), F.Id("H")), CloseBracket, Comma, Sp,
        OpenBracket, Call("CompleteSpace", F.Id("H")), CloseBracket, Comma,
        RowBreak, Grp(), conclusion, Dot));

    private static Formula Bound() => Call("ofReal", Seq(Frac, Grp(Sq(Call("norm", F.Id("r")))), Grp(D(2))));
    private static Formula Admissible(Formula path) => Call("A", F.Id("M"), F.Id("x"), path);
    private static Formula Sq(Formula value) => Seq(Grp(value), Caret, Grp(D(2)));
    private static Formula Lambda(string name, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(name), Colon, Sp, F.Id("Real"), Sp, Mapsto, Sp, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
