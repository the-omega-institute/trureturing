using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class AnnularSecondZeroDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/AnnularSecondZero.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula And(params Formula[] xs)
    {
        var b = xs[^1];
        for (var i = xs.Length - 2; i >= 0; --i) b = new Formula.Logic(xs[i], FormulaLogicOperator.And, b);
        return b;
    }
    private static Formula Bind((string Name, Formula Type)[] xs, Formula b)
    {
        for (var i = xs.Length - 1; i >= 0; --i) b = All(xs[i].Name, xs[i].Type, b);
        return b;
    }
    private static Formula Inst(string s, params Formula[] xs) =>
        F.Seq(F.OpenBracket, Call(s, xs), F.CloseBracket, F.Sp);
    private static Formula Norm(Formula x) => Call("norm", x);
    private static Formula Eq(Formula x, Formula y) => F.Seq(x, F.Sp, F.Eq, F.Sp, y);
    private static Formula Ne(Formula x, Formula y) => F.Seq(x, F.Sp, F.Neq, F.Sp, y);
    private static Formula Lt(Formula x, Formula y) => F.Seq(x, F.Sp, F.Lt, F.Sp, y);
    private static Formula Le(Formula x, Formula y) => F.Seq(x, F.Sp, F.Le, F.Sp, y);

    private static Formula ExteriorStatement()
    {
        var E = Id("E"); var q = Id("q"); var a = Id("a"); var c = Id("c");
        var M = Id("M"); var L = Id("L"); var x = Id("x"); var b = Id("b");
        var zero = F.D(0); var real = Id("Real");
        var statement = Imp(And(Call("Continuous", q), Ne(c, zero),
            All("x", E, Imp(Le(M, Norm(x)), Eq(Call("q", x), c))),
            Eq(Call("q", a), zero),
            Call("HasFDerivAt", q, Call("toContinuousLinearMap", L), a)),
            Ex("b", E, And(Ne(b, a), Eq(Call("q", b), zero))));
        return All("E", Id("Types"), F.Seq(
            Inst("NormedAddCommGroup", E), Inst("NormedSpace", real, E),
            Inst("FiniteDimensional", real, E), Inst("Nontrivial", E),
            Bind([("q", new Formula.TypeArrow(E, E)), ("a", E), ("c", E), ("M", real),
                ("L", Call("ContinuousLinearEquiv", real, E, E))], statement)));
    }

    private static Formula AnnularStatement()
    {
        var complex = Id("Complex"); var real = Id("Real"); var f = Id("f");
        var a = Id("a"); var r = Id("r"); var R = Id("R"); var L = Id("L");
        var z = Id("z"); var b = Id("b"); var zero = F.D(0);
        var annulus = Call("SetDifference", Call("closedBall", zero, R), Call("ball", zero, r));
        var boundary = All("z", complex, Imp(Or(Eq(Norm(z), r), Eq(Norm(z), R)),
            Lt(Call("re", Call("f", z)), zero)));
        var statement = Imp(And(Lt(zero, r), Lt(r, Norm(a)), Lt(Norm(a), R),
            Call("ContinuousOn", f, annulus), Eq(Call("f", a), zero),
            Call("HasFDerivAt", f, Call("toContinuousLinearMap", L), a), boundary),
            Ex("b", complex, And(Lt(r, Norm(b)), Lt(Norm(b), R), Ne(b, a), Eq(Call("f", b), zero))));
        return Bind([("f", new Formula.TypeArrow(complex, complex)), ("a", complex),
            ("r", real), ("R", real), ("L", Call("ContinuousLinearEquiv", real, complex, complex))], statement);
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A regular zero forces another zero when the exterior is constant or both annular boundaries lie in a strict half-plane.",
        H("A second zero from the sphere obstruction"), Blocks(
            Paragraph(Text("All derivatives in this document are Frechet derivatives over the real field. ContinuousLinearEquiv denotes an invertible continuous real linear map, and toContinuousLinearMap is its underlying derivative operator. The norm is the given real norm; no inner product is needed in the first result.")),
            Describe.Lean(DescribeId.Create("constant-exterior-second-zero"),
                DeclarationHandle.Create(Owner + "constantExterior_second_zero"),
                H("A constant exterior cannot enclose just one regular zero"),
                StatementSource.FromAuthor(F.Disp(ExteriorStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let E be any nontrivial finite-dimensional real normed space, q a continuous map E to E, and a and c points of E with c nonzero. The real threshold M is arbitrary. Assume q(x)=c whenever M is at most norm(x), q(a)=0, and the ordinary derivative of q at a is the invertible continuous linear map L. Then q has a zero b distinct from a.")),
                    Paragraph(Text("Compose q with the inverse of L. Its derivative at a is the identity, so the derivative remainder gives norm(p(a+h)-h) at most norm(h)/2 on a sufficiently small closed ball. On its boundary the straight segment from h to p(a+h) never vanishes. Normalizing that segment gives a homotopy from the unit-sphere identity to the normalized local image.")),
                    Paragraph(Text("If a were the only zero, expand the positive sphere radius about a until every image point lies in the constant exterior. The normalized image would then be homotopic to a constant. Joining these homotopies contracts the unit sphere, contradicting TauCeti.not_contractibleSpace_sphere. This includes ambient dimension one and uses only the ordinary derivative at the designated point."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("annular-second-zero"),
                DeclarationHandle.Create(Owner + "annular_second_zero"),
                H("Two left-half-plane boundary circles force a second interior zero"),
                StatementSource.FromAuthor(F.Disp(AnnularStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The map f is a total function on the complex plane, with continuity required only on closedBall(0,R) minus ball(0,r). SetDifference denotes this set difference. The radii satisfy 0<r<norm(a)<R. The point a is a zero with invertible real derivative L. On each of the two boundary circles, the real part of f is strictly negative. The conclusion gives b with r<norm(b)<R, b distinct from a, and f(b)=0.")),
                    Paragraph(Text("Write rho=norm(z), and radially clamp rho to the interval from r to R. Multiply f of that clamped point by w, where w is the product of clamp(2 rho/r-1) and clamp(R+1-rho), and clamp(t)=max(0,min(1,t)). Add (1-w) times minus one. The resulting map q agrees with f on the closed annulus, equals minus one for rho at most r/2 or at least R+1, and is continuous everywhere.")),
                    Paragraph(Text("Away from zero the radial clamp and the weights are continuous and the clamped point stays in the closed annulus, including all seams. Near zero the weight vanishes and q is constant, so no division at zero enters the continuity argument. On an inner or outer collar the clamped point lies on the corresponding boundary circle. Both f of that point and minus one have negative real part, so their convex combination is nonzero.")),
                    Paragraph(Text("Because a is strictly interior, q agrees with f on a neighborhood of a and inherits its ordinary real derivative. Apply the constant-exterior result. Every zero of q lies strictly in the original annulus, so its second zero is a second zero of f there. No holomorphicity, strict differentiability, isolated-zero condition or finiteness of other zeros is assumed.")),
                    Paragraph(Text("These are static topological consequences of the classical sphere obstruction, with no originality claim. Applying them to a reconstruction residual still requires an actual residual, its continuity, the two boundary inequalities, an interior zero and its invertible real derivative. They provide no dynamics, time group, energy, physical clock or thermodynamic conclusion."))),
                DescribeRole.Theorem))));
}
