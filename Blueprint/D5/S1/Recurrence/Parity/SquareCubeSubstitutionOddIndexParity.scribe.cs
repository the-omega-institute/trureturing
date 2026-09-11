using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class SquareCubeSubstitutionOddIndexParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2025a389472");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every odd-index coefficient beyond the first in OEIS A389472 is even.",
        H("Hanna's Odd-Index Parity Conjecture"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a389472 gives the generating equation "
                + "A(x)=A(x^2+x^3)/x^2-1 and conjectures a(2n-1)=0 modulo two for n>1. "
                + "The formal equation is x^2(A(x)+1)=A(x^2+x^3), with a(0)=0 and "
                + "a(1)=a(2)=1. The equation forces a(1)=1 but leaves a(2) free; "
                + "the seed a(2)=1 selects the sequence in the entry. The separate "
                + "conjecture modulo three is not asserted here.")),
            Paragraph(Text("All indices and exponents are natural numbers, and subtraction "
                + "in an index is natural subtraction. Fin(n) consists of k with 0<=k<n, "
                + "read as natural numbers in coefficients and exponents; range(n) is the "
                + "same finite set of natural indices. The function div is natural integer "
                + "division. Values of a and binomial coefficients in products are integers. "
                + "PowerSeries(Z) is the formal power-series ring with indeterminate X. "
                + "The notation subst(B,Q) means B composed with Q, coeff(n,B) is coefficient n, "
                + "and mk(a) constructs the series with coefficient function a.")),
            Node("a", "The normalized coefficient sequence", SequenceFormula(),
                "The three seeds and a recursion using only indices below n+3 define an "
                + "integer sequence. The substituted powers determine its recursion kernel.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "Coefficient n of generatingSeries is a(n).", DescribeRole.Definition),
            Node("generating_equation", "The functional equation and all three seeds", EquationFormula(),
                "The kth power of X^2+X^3 has no coefficients below degree 2k. Thus each "
                + "substituted coefficient is a finite sum. The recursion establishes the "
                + "equation in degrees at least five; the three prescribed seeds establish "
                + "the remaining degrees and the displayed normalization."),
            Node("generating_unique", "Uniqueness with the prescribed seeds", UniqueFormula(),
                "For n at least three, coefficient n+2 of the functional equation determines "
                + "coefficient n using only smaller indices. Strong induction starting from "
                + "the three seeds proves equality with generatingSeries."),
            Node("coeff_recurrence", "The binomial coefficient recurrence", RecurrenceFormula(),
                "Extract coefficient n+2 from the proved generating equation and factor "
                + "(X^2+X^3)^k as X^(2k)(1+X)^k. The binomial coefficient formula gives "
                + "the displayed sum, whose upper bound includes exactly 2k<=n+2."),
            Node("hanna_conjecture", "The first A389472 conjecture", ConjectureFormula(),
                "For an odd index m>=3, the lower binomial index m+2-2k is odd. If k is "
                + "even, the identity j choose(k,j)=k choose(k-1,j-1) makes the binomial "
                + "coefficient even. If k is odd and at least three, then k<m, so strong "
                + "induction makes a(k) even. The only remaining odd index is k=1, whose "
                + "binomial coefficient is choose(1,m)=0. Every summand is therefore even.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a389472-square-cube-substitution-odd-index-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a389472-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula X() => F.Id("X");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Inner() => Add(Power(X(), D(2)), Power(X(), D(3)));
    private static Formula Coefficient(Formula index, Formula series) => Call("coeff", index, series);
    private static Formula A(Formula index) => Call("a", index);
    private static Formula SumFin(Formula bound, Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Seq(K(), Colon, Sp, Call("Fin", bound))),
            Sp, Parenthesized(summand));
    private static Formula Equation(Formula series) =>
        Equal(Mul(Power(X(), D(2)), Parenthesized(Add(series, D(1)))),
            Call("subst", series, Inner()));

    private static Formula SequenceFormula() => Disp(new Formula.Aligned([
        Seq(Named("a"), Colon, Sp, Naturals(), Sp, To, Sp, Integers()),
        Equal(A(D(0)), D(0)),
        Equal(A(D(1)), D(1)),
        Equal(A(D(2)), D(1)),
        Seq(Bound("n", Naturals()), Equal(A(Add(N(), D(3))),
            SumFin(Add(N(), D(3)), Mul(A(K()),
                Coefficient(Add(N(), D(5)), Power(Parenthesized(Inner()), K()))))))
    ]));

    private static Formula GeneratingFormula() => Disp(Seq(
        Generating(), Colon, Sp, Series(), Comma, Sp,
        Equal(Generating(), Call("mk", Named("a")))));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", Generating()), D(0)),
        Conjunction(Equal(Coefficient(D(1), Generating()), D(1)),
            Conjunction(Equal(Coefficient(D(2), Generating()), D(1)), Equation(Generating())))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Implication(Equal(Coefficient(D(1), b), D(1)),
                    Implication(Equal(Coefficient(D(2), b), D(1)),
                        Implication(Equation(b), Equal(b, Generating())))))));
    }

    private static Formula RecurrenceFormula()
    {
        Formula degree = Subtract(Add(N(), D(2)), Mul(D(2), K()));
        Formula bound = Add(Call("div", N(), D(2)), D(2));
        Formula sum = Seq(new Formula.Subscript(F.Sum,
                Seq(K(), Sp, InMacro, Sp, Call("range", bound))), Sp,
            Parenthesized(Mul(A(K()), Call("choose", K(), degree))));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(3), Sp, Le, Sp, N()), Equal(A(N()), sum))));
    }

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()),
            Seq(D(2), Sp, Mid, Sp, A(Subtract(Mul(D(2), N()), D(1)))))));
}
