using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class NonobtuseFamilyFixedVectorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/NonobtuseFamilyFixedVector.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty set of unit vectors with pairwise nonnegative inner products in a finite-dimensional real inner product space has a nonzero least-norm point in its closed convex hull, and every linear isometry equivalence mapping the set into itself fixes that point.",
        H("A fixed vector for a nonobtuse family of unit vectors"),
        Blocks(
            Node("exists-fixed", "exists_fixed_ne_zero_of_pairwise_inner_nonneg",
                "The least-norm point of the closed convex hull is nonzero and fixed",
                StatementSource.FromAuthor(FixedVectorFormula()), AssessedProvenance.FromRepo(),
                "Let E be a finite-dimensional real inner product space and S a nonempty set of unit vectors of E with <s, t> >= 0 for all s and t in S. "
                    + "Write K for the closure of the convex hull of S. "
                    + "Then K contains a point m with m different from 0, ||m|| <= ||x|| and ||m||^2 <= <x, m> for every x in K, and U m = m for every linear isometry equivalence U of E onto itself whose image of S is contained in S. "
                    + "By Caratheodory's theorem every point x of the convex hull of S is a convex combination of at most finrank E + 1 members of S with positive weights w_i. "
                    + "Since all cross terms are nonnegative and the members have norm one, ||x||^2 is at least the sum of the squares of the weights, which by the Cauchy-Schwarz inequality is at least 1 / (finrank E + 1). "
                    + "This bound passes to the closure, so K does not contain 0. "
                    + "The set K is nonempty, closed and convex in a complete space, so it has a point m of least norm, which is therefore nonzero. "
                    + "The variational characterization of the nearest point to 0 gives <0 - m, x - m> <= 0 for x in K, that is ||m||^2 <= <x, m>; together with <x, m> <= ||x|| ||m|| and ||m|| > 0 it gives ||m|| <= ||x||. "
                    + "If x lies in K and ||x|| = ||m||, then ||x - m||^2 = 2 ||m||^2 - 2 <x, m> <= 0, so x = m. "
                    + "A linear isometry equivalence U with image of S inside S maps the convex hull of S into itself by linearity and, being continuous, maps K into K. "
                    + "Hence U m lies in K and has the norm of m, so U m = m.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nonobtuse-family-fixed-vector-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Ap(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Inner(Formula x, Formula y) =>
        new Formula.Subscript(Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle), Reals);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Paren(params Formula[] items) => Seq([Open, .. items, Close]);

    private static Formula FixedVectorFormula()
    {
        Formula e = F.Id("E"), s = F.Id("S"), m = F.Id("m"), x = F.Id("x"), u = F.Id("U");
        Formula sv = F.Id("s"), tv = F.Id("t");
        Formula hull = Call("closure", Call("convexHull", Reals, s));
        Formula unit = Paren(Forall, Sp, sv, Sp, InMacro, Sp, s, Comma, Sp,
            Norm(sv), Sp, Eq, Sp, D(1));
        Formula nonobtuse = Paren(Forall, Sp, sv, Sp, InMacro, Sp, s, Comma, Sp,
            Forall, Sp, tv, Sp, InMacro, Sp, s, Comma, Sp, D(0), Sp, Leq, Sp, Inner(sv, tv));
        Formula least = Paren(Forall, Sp, x, Sp, InMacro, Sp, hull, Comma, Sp,
            Norm(m), Sp, Leq, Sp, Norm(x));
        Formula variational = Paren(Forall, Sp, x, Sp, InMacro, Sp, hull, Comma, Sp,
            new Formula.Power(Norm(m), D(2)), Sp, Leq, Sp, Inner(x, m));
        Formula fixedPoint = Paren(Forall, Sp, u, Colon, Sp, Call("LinearIsometryEquiv", Reals, e, e), Comma, Sp,
            Call("image", u, s), Sp, Subseteq, Sp, s, Sp, Rightarrow, Sp, Ap(u, m), Sp, Eq, Sp, m);
        return Disp(Seq(
            Forall, Sp, e, Colon, Sp, TypeStar, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", Reals, e), CloseBracket, Comma, Sp,
            OpenBracket, Call("FiniteDimensional", Reals, e), CloseBracket, Comma, Sp,
            Forall, Sp, s, Colon, Sp, Call("Set", e), Comma, Sp,
            Call("Nonempty", s), Sp, Rightarrow, Sp, unit, Sp, Rightarrow, Sp, nonobtuse, Sp, Rightarrow, Sp,
            Exists, Sp, m, Colon, Sp, e, Comma, Sp,
            m, Sp, Neq, Sp, D(0), Sp, Land, Sp, m, Sp, InMacro, Sp, hull, Sp, Land, Sp,
            least, Sp, Land, Sp, variational, Sp, Land, Sp, fixedPoint));
    }
}
