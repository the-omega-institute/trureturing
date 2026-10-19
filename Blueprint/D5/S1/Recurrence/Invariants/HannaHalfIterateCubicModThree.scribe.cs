using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaHalfIterateCubicModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2005a107099");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized half-iterate of X + 4 X cubed has integral coefficients supported modulo three on powers of three.",
        H("Hanna's Half-Iterate Conjecture Modulo Three"),
        Blocks(
            Paragraph(Text("PowerSeries denotes formal power series. The indeterminate is X, "
                + "coeff(n,A) is its degree-n coefficient, and PowerSeries.subst(A,A) is composition. "
                + "Indices are natural numbers. The integer m in the formulas is cast to the rationals "
                + "when compared with a rational coefficient; Int.ModEq is integer congruence.")),
            Node("IsGF", "The normalized odd half-iterate", Disp(All("A", Series(),
                Equal(Call("IsGF", F.Id("A")), Parenthesized(GfBody(F.Id("A")))))),
                "The unpaginated OEIS A107099 Name states: \"G.f. satisfies A(A(x)) = x + 4*x^3, "
                + "where A(x) = Sum_{n>=0} a(n)*x^(2*n+1).\" The Example states: "
                + "\"A(x) = 1*x + 2*x^3 - 6*x^5 + 36*x^7 - 266*x^9 + 2028*x^11 - 13596*x^13 +-...\" "
                + "The carrier is PowerSeries over the rationals; the even coefficients vanish and "
                + "the linear coefficient is one, as in the offset-zero sequence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The coefficient congruence", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "The unpaginated OEIS A107099 Comments state: \"Coefficients [x^n] A(x) = 0 (mod 3) "
                + "except at n = 3^k (conjecture).\" Existence is asserted, and every IsGF series "
                + "has integer coefficients. The exponent n ranges over all natural numbers. "
                + "No nonvanishing assertion at powers of three is included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integrality and the congruence at every degree", Disp(ClaimBody()),
                "Correct successive degrees of an integer series beginning with X. A series of "
                + "the form X + 2B has compositional residual divisible by four, so each correction "
                + "is even. The compatible coefficients define an integral solution. The "
                + "degree-n change in the compositional square is twice the degree-n change in "
                + "the series, proving uniqueness by induction. Reflection through minus X "
                + "then proves oddness. Over ZMod(3), Frobenius preserves support on powers of "
                + "three, and substitution preserves this support as well. Strong induction "
                + "compares the solution with its truncation and forces every other coefficient "
                + "to vanish. Rational uniqueness transfers these integer coefficients to every IsGF series.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("hanna-half-iterate-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Arrow(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula GfBody(Formula a) => And(
        All("n", Naturals(), Equal(Call("coeff", Mul(D(2), F.Id("n")), a), D(0))),
        And(Equal(Call("coeff", D(1), a), D(1)),
            Equal(App(Qualified("PowerSeries", "subst"), a, a),
                Add(F.Id("X"), Mul(D(4), Pow(F.Id("X"), D(3)))))));
    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var m = F.Id("m");
        var offSupport = Seq(Neg, Parenthesized(Some("k", Naturals(), Equal(n, Pow(D(3), F.Id("k"))))));
        return And(Some("A", Series(), Call("IsGF", a)),
            All("A", Series(), Arrow(Call("IsGF", a), All("n", Naturals(),
                Some("m", Integers(), And(Equal(Call("coeff", n, a), Parenthesized(Seq(m, Colon, Sp, Rationals()))),
                    Arrow(offSupport, App(Qualified("Int", "ModEq"), D(3), m, D(0)))))))));
    }
}
