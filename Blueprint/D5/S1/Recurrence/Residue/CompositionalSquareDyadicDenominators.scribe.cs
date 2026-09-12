using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class CompositionalSquareDyadicDenominatorsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/scheuerle2025a381670");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every reduced denominator of the normalized compositional-square series is a power of two.",
        H("Dyadic Denominators of OEIS A381670"),
        Blocks(
            Paragraph(Text(
                "Thomas Scheuerle's entry of March 3, 2025, cited in scheuerle2025a381670, "
                + "defines A by x(A(x)+1)=A(A(x)), with constant coefficient zero and "
                + "linear coefficient one. A381669 records the reduced numerators; "
                + "A381670 records the positive reduced denominators.")),
            Paragraph(Text(
                "A denotes generatingSeries, f(n) its rational coefficient, and X the formal "
                + "variable. The notation coeff(n,P) means the coefficient of X^n in P, "
                + "C embeds a scalar as a constant series, subst(P,Q) means P(Q(X)), "
                + "and rescale(c,P) means P(cX). The integral series I is built from "
                + "compatible approximations P_n. The map iota sends integers to rationals. "
                + "All indices are natural numbers; subtraction in an exponent is natural "
                + "subtraction. The operation div below is integer division.")),
            Node("generatingSeries", "Construction by compatible integral approximations",
                ConstructionFormula(),
                "Set E(P)=P(P(X))-X-4XP. Starting with P_0=X, correct degree n+2 "
                + "by subtracting half its residual. The triangular composition identity "
                + "gives multiplier two in that degree and preserves every lower degree. "
                + "If P-X=2Q, then Q(P)-Q(X) is divisible by two, because P^j-X^j "
                + "is divisible by P-X. Therefore E(P) is divisible by four and each "
                + "correction is even. The stable coefficients define I. Scaling back "
                + "gives A=4I(X/4), with the integer coefficients embedded in the rationals.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("f", "The rational coefficient sequence", CoefficientFormula(),
                "The sequence f is extracted from the constructed formal series. Its "
                + "reduced denominators are the terms of A381670, with denominator one "
                + "for any zero coefficient.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("functional_equation", "The defining functional equation", EquationFormula(),
                "The limit of the corrected approximations satisfies I(I(X))=X+4XI(X). "
                + "Mapping to rational coefficients and conjugating by the linear scaling "
                + "gives exactly X(A+1)=A(A(X)), with the stated constant and linear terms.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("uniqueness", "Uniqueness with the specified normalization", UniquenessFormula(),
                "If two normalized series agree below degree n, their compositional "
                + "squares differ there by twice their coefficient difference. The "
                + "right side X+XB depends only on the preceding coefficient. Induction "
                + "therefore forces equality at every degree over the rationals.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("rescaled_even", "The rescaled coefficients are even integers", EvenFormula(),
                "Every integral approximation differs from X by twice an integer series. "
                + "This persists in the compatible limit I. Undoing the scaling identifies "
                + "its degree-n coefficient with 4^(n-1)f(n) for n at least two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("scheuerle_conjecture", "Every denominator is a power of two", ConjectureFormula(),
                "For n at least two the even-integer invariant writes f(n) as an integer "
                + "divided by 4^(n-1). Its reduced denominator divides that power of two, "
                + "so it is itself a power of two. At indices zero and one the coefficients "
                + "are zero and one, both with denominator one. No nonzero-coefficient "
                + "restriction is imposed.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a381670-compositional-square-dyadic-denominators"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a381670-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula ConstructionFormula()
    {
        var n = F.Id("n");
        var p = Call("P", n);
        var degree = Add(n, D(2));
        var residual = Call("coeff", degree, Call("E", p));
        var correction = Seq(Minus, Call("div", residual, D(2)));
        return Disp(new Formula.Aligned([
            Equal(A(), Mul(Call("C", D(4)), Call("rescale", new Formula.Fraction(D(1), D(4)),
                Call("map", Named("iota"), F.Id("I"))))),
            Equal(F.Id("I"), Call("mk", Seq(n, Sp, Mapsto, Sp, Call("coeff", n, Call("P", n))))),
            Equal(Call("P", D(0)), X()),
            Universal("n", "N", Equal(Call("P", Add(n, D(1))),
                Add(p, Mul(Call("C", correction), Power(X(), degree))))),
            Universal("P", "Z", Equal(Call("E", F.Id("P")),
                Subtract(Subtract(Call("subst", F.Id("P"), F.Id("P")), X()),
                    Mul(Mul(D(4), X()), F.Id("P")))), true)
        ]));
    }

    private static Formula CoefficientFormula() => Disp(Universal("n", "N",
        Equal(Call("f", F.Id("n")), Call("coeff", F.Id("n"), A()))));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(0)), Conjunction(
        Equal(Call("coeff", D(1), A()), D(1)), Equation(A()))));

    private static Formula UniquenessFormula()
    {
        var b = F.Id("B");
        return Disp(Universal("B", "Q", Implication(
            Equal(Call("constantCoeff", b), D(0)), Implication(
            Equal(Call("coeff", D(1), b), D(1)), Implication(
            Equation(b), Equal(b, A())))), true));
    }

    private static Formula EvenFormula()
    {
        var n = F.Id("n");
        var z = F.Id("z");
        return Disp(Universal("n", "N", Implication(Seq(D(2), Sp, Le, Sp, n),
            Seq(Exists, Sp, z, Sp, InMacro, Sp, Field("Z"), Comma, Sp,
                Equal(Mul(Power(D(4), Subtract(n, D(1))), Call("f", n)), Call("iota", Mul(D(2), z)))))));
    }

    private static Formula ConjectureFormula() => Disp(Universal("k", "N",
        Seq(Exists, Sp, F.Id("e"), Sp, InMacro, Sp, Field("N"), Comma, Sp,
            Equal(Call("den", Call("f", F.Id("k"))), Power(D(2), F.Id("e"))))));

    private static Formula A() => F.Id("A");
    private static Formula X() => F.Id("X");
    private static Formula Field(string symbol) => Seq(Mathbb, Grp(F.Id(symbol)));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Equation(Formula series) =>
        Equal(Mul(X(), Parenthesized(Add(series, D(1)))), Call("subst", series, series));
    private static Formula Universal(string name, string field, Formula body, bool series = false) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp,
            series ? Seq(Field(field), OpenBracket, OpenBracket, X(), CloseBracket, CloseBracket) : Field(field),
            Comma, Sp, body);
}
