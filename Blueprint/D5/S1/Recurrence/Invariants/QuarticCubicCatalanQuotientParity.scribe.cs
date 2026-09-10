using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class QuarticCubicCatalanQuotientParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2025a384270");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A384270 are odd exactly at powers of two.",
        H("Hanna's Quartic-Cubic Quotient Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a384270 specifies "
                + "A(x)=A(x^4+4xA(x)^4)/A(x^3+3xA(x)^3) and conjectures the parity "
                + "support. The denominator has zero constant coefficient and is not a "
                + "unit in the integer power-series ring. The defining equation below "
                + "is therefore cross-multiplied, with A(0)=0 and a(1)=1.")),
            Paragraph(Text("Indices are natural numbers. PowerSeries(Z) is the integer "
                + "formal power-series ring, X is its indeterminate, and all series powers "
                + "are ring powers. The notation subst(B,U) substitutes U into B; coeff(n,B) "
                + "extracts a coefficient, and mk constructs a series from its coefficient "
                + "function. The auxiliary symbols b, approximation, T, and u describe "
                + "the private construction used in the definition of a.")),
            Node("a", "The integral coefficient construction", CoefficientFormula(),
                "The approximations start at one and apply T. Their constant coefficient "
                + "remains one. Agreement below degree d improves to agreement below "
                + "degree d+1, since each inner series is divisible by X squared and "
                + "the uncancelled differences carry an additional X. The diagonal "
                + "coefficients define b, and a is the coefficient function of Xb. "
                + "Every operation in this construction is integral; no division occurs.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The integer generating series has coefficient function a.",
                DescribeRole.Definition),
            Node("generating_equation", "The normalized functional equation", EquationFormula(),
                "The diagonal limit is a fixed point of T. Writing A=Xb and cancelling "
                + "X^4 identifies this fixed-point equation with the displayed "
                + "cross-multiplied equation. The constant and linear coefficients "
                + "follow from the constant coefficient of b being one."),
            Node("generating_unique", "Uniqueness of the integer series", UniqueFormula(),
                "Factor any series with zero constant coefficient as Xb. The linear "
                + "coefficient hypothesis gives b(0)=1. Cancelling X^4 turns its equation "
                + "into the fixed-point identity for T. Induction on coefficient "
                + "agreement proves uniqueness. This argument also holds over ZMod(2)."),
            Node("hanna_conjecture", "The parity conjecture", HannaFormula(),
                "Over ZMod(2), let C be the compositional inverse of X+X^2. Then "
                + "C+C^2=X, so X^3+XC^3=C^3+C^6. Substituting C^3 into the left inverse "
                + "identity gives C(C^3+C^6)=C^3. Frobenius gives C(X^4)=C^4, hence C "
                + "satisfies the reduced functional equation. Uniqueness identifies "
                + "the reduction of generatingSeries with C. Its quadratic identity "
                + "makes the coefficient at an even index equal to that at half the "
                + "index and makes every odd index above one vanish. Strong induction "
                + "gives exactly the powers of two.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a384270-quartic-cubic-catalan-quotient-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a384270-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
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
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Approx(Formula depth) => Call("approximation", depth);
    private static Formula Factor(Formula p, Formula b) =>
        Parenthesized(Add(D(1), Mul(Mul(p, X()), Power(b, p))));
    private static Formula Inner(Formula p, Formula b) => Call("u", p, b);
    private static Formula Transform(Formula b) =>
        Subtract(Add(b, Mul(Factor(D(4), b), Call("subst", b, Inner(D(4), b)))),
            Mul(Mul(b, Factor(D(3), b)), Call("subst", b, Inner(D(3), b))));
    private static Formula Argument(Formula p, Formula a) =>
        Add(Power(X(), p), Mul(Mul(p, X()), Power(a, p)));
    private static Formula Equation(Formula a) =>
        Equal(Mul(a, Call("subst", a, Argument(D(3), a))),
            Call("subst", a, Argument(D(4), a)));

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula j = F.Id("j");
        Formula p = F.Id("p");
        Formula b = F.Id("b");
        Formula t = F.Id("t");
        return Disp(new Formula.Aligned([
            Seq(Bound("n", Naturals()), Equal(Call("a", n), Call("coeff", n, Mul(X(), b)))),
            Equal(b, Call("mk", Parenthesized(Seq(j, Colon, Sp, Naturals(), Sp, Mapsto, Sp,
                Call("coeff", j, Approx(Add(j, D(1)))))))),
            Equal(Approx(D(0)), D(1)),
            Seq(Bound("d", Naturals()), Equal(Approx(Add(d, D(1))), Call("T", Approx(d)))),
            Seq(Bound("t", Series()), Equal(Call("T", t), Transform(t))),
            Seq(Bound("p", Naturals()), Bound("t", Series()),
                Equal(Inner(p, t), Mul(Power(X(), p), Factor(p, t))))
        ]));
    }

    private static Formula GeneratingFormula() => Disp(Equal(Generating(), Call("mk", F.Id("a"))));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", Generating()), D(0)), Conjunction(
            Equal(Call("coeff", D(1), Generating()), D(1)), Equation(Generating()))));

    private static Formula UniqueFormula()
    {
        Formula f = F.Id("f");
        return Disp(Seq(Bound("f", Series()),
            Implication(Equal(Call("constantCoeff", f), D(0)),
                Implication(Equal(Call("coeff", D(1), f), D(1)),
                    Implication(Equation(f), Equal(f, Generating()))))));
    }

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula support = Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Equal(n, Power(D(2), k)));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Le, Sp, n), Parenthesized(
                Seq(Call("Odd", Call("a", n)), Sp, Iff, Sp, Parenthesized(support))))));
    }
}
