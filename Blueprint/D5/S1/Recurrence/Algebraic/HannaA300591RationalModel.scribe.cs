using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA300591RationalModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/hanna2018a300595");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar exponentials give unique normalized rational solutions of triangular equations and a local valuation bound from the strict prefix.",
        H("Rational scalar exponential equations"), Blocks(
            Node("expSeries", "Formal scalar exponential",
                All("t", Q(), All("F", Series(), Eqn(Call("expSeries", V("t"), V("F")),
                    Call("subst", Mul(Call("C", V("t")), V("F")), Call("exp", Q()))))),
                "The operation is substitution into the formal exponential over Q. " +
                "The first argument of PowerSeries.subst is the inner series. " +
                "When the inner series has constant coefficient zero, this is exp(t F).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("triangular_exists_unique", "Unique rational normalized triangular source",
                TriangularBody(),
                "The functions lam and mu are arbitrary rational-valued functions on the natural numbers, " +
                "and lam(n) is nonzero for every n>=1. A degree-n change of the exponent changes the " +
                "degree-n exponential coefficient by lam(n) times that change and preserves all lower " +
                "coefficients. The derivative recurrence and coefficient agreement give this residual " +
                "identity. PowerSeriesNormalizedContraction.exists_unique_fixed then constructs the " +
                "unique normalized solution over Q. The hypotheses concern rational series in arbitrary degree. " +
                "Taking lam(n)=mu(n)=n^3 gives the rational characterization used by HannaA300595Integrality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("local_automatic_bound", "Local valuation from the strict prefix",
                LocalBoundBody(),
                "Truncation before degree n preserves the exponential coefficients below n. " +
                "If h=v_p(t)>=1, the degree-(n-1) exponential coefficient of the truncated series " +
                "has valuation at least h when nonzero. The degree-n exponential coefficient " +
                "of that series has valuation at least 2h-1 when nonzero, since its zeroth and first " +
                "power contributions vanish. Both estimates use v_p(j!)<=j-1 for positive j. " +
                "The degree-n residual identity and the given exponential equation express " +
                "the original coefficient as the difference of the first truncated coefficient " +
                "and the second divided by t. This yields the displayed lower bound. " +
                "The cubic integrality proof applies it with t=n^3 at every prime dividing n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hannaa300591-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Series() => Call("PowerSeries", Q());
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Unique(string name, Formula type, System.Func<Formula, Formula> property) =>
        Ex(name, type, And(property(V(name)),
            All("G", type, Imp(property(V("G")), Eqn(V("G"), V(name))))));
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula TriangularBody()
    {
        var lam = new Formula.Apply(V("lam"), [V("n")]);
        var mu = new Formula.Apply(V("mu"), [V("n")]);
        var premise = All("n", N(), Imp(Leq(D(1), V("n")), Not(Eqn(lam, D(0)))));
        Formula Source(Formula f) => And(Eqn(Call("constantCoeff", f), D(0)),
            All("n", N(), Imp(Leq(D(1), V("n")), Eqn(
                Coeff(V("n"), Call("expSeries", lam, f)),
                Mul(mu, Coeff(Sub(V("n"), D(1)), Call("expSeries", lam, f)))))));
        return All("lam", Call("Function", N(), Q()),
            All("mu", Call("Function", N(), Q()),
                Imp(premise, Unique("F", Series(), f => Par(Source(f))))));
    }

    private static Formula Not(Formula a) => Seq(Neg, Par(a));
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LocalBoundBody()
    {
        var p = V("p");
        var t = V("t");
        var f = V("F");
        var n = V("n");
        var a = Coeff(n, f);
        var exp = Call("expSeries", t, f);
        Formula Val(Formula q) => Call("padicValRat", p, q);
        var prefix = All("j", N(), Imp(Lt(V("j"), n),
            Call("IsRIntegralRat", p, Coeff(V("j"), f))));
        var equation = Eqn(Coeff(n, exp), Mul(t, Coeff(Sub(n, D(1)), exp)));
        var coefficientBound = Imp(Not(Eqn(a, D(0))), Leq(Sub(Val(t), D(1)), Val(a)));
        var normalized = Imp(Eqn(Call("constantCoeff", f), D(0)),
            All("n", N(), Imp(Leq(D(2), n), Imp(prefix, Imp(equation, coefficientBound)))));
        var scalar = All("t", Q(), Imp(Not(Eqn(t, D(0))),
            Imp(Leq(D(1), Val(t)), All("F", Series(), normalized))));
        return All("p", N(), Imp(Call("Prime", p), scalar));
    }
}
