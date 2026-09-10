using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HalfScaledReflectionParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2025a389540");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd coefficients of OEIS A389540 occur exactly at powers of two.",
        H("Hanna's Half-Scaled Reflection Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a389540 defines A(x) by "
                + "A(x)^2=A(2x-2A(x))/2 and conjectures that a(n) is odd exactly when "
                + "n is a power of two. The integer series below has constant coefficient "
                + "zero, linear coefficient one, and satisfies the equation after "
                + "multiplication by two.")),
            Paragraph(Text("All indices are natural numbers, and r and a take integer values. "
                + "R denotes inverseSeries and A denotes generatingSeries in the integer "
                + "formal power-series ring PowerSeries(Z), with indeterminate X. "
                + "The operator mk constructs a series from its coefficient function, "
                + "coeff(n,B) extracts a coefficient, and subst(B,C) substitutes C into B. "
                + "The notation inv(R) denotes Mathlib's substInvOfIsUnit applied to the "
                + "proved unit linear coefficient of R; it is a compositional inverse. "
                + "The operator div is integer Euclidean division, and subNat is natural "
                + "subtraction truncated at zero. Multiplication by two is repeated addition.")),
            Node("r", "The inverse coefficients", InverseCoefficientFormula(),
                "The recursion fixes r(0)=0 and r(1)=1. Every other even index is reduced "
                + "to half its value with the displayed integral power-of-two multiplier; "
                + "every other odd index has coefficient zero.", DescribeRole.Definition),
            Node("inverseSeries", "The inverse series", Disp(Equal(R(), Call("mk", F.Id("r")))),
                "The series R has coefficient function r. Its constant coefficient is zero "
                + "and its linear coefficient is one, so Mathlib's integral compositional "
                + "inverse applies.", DescribeRole.Definition),
            Node("a", "The OEIS coefficients", CoefficientFormula(),
                "The coefficient a(n) is the nth integer coefficient of the compositional "
                + "inverse of R.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series", Disp(Equal(A(), Call("mk", F.Id("a")))),
                "The series A has coefficient function a and is the compositional inverse "
                + "of R in both orders.", DescribeRole.Definition),
            Node("generating_equation", "The defining equation and normalization", EquationFormula(),
                "The recursion for r gives R(2X^2)=2R-2X coefficient by coefficient. "
                + "Substituting A and using R(A)=X gives R(2A^2)=2X-2A. Composing with "
                + "A gives the displayed equation, together with the two normalization conditions."),
            Node("generating_unique", "Uniqueness among normalized integer series", UniqueFormula(),
                "A normalized integer solution B has an integral compositional inverse S. "
                + "Its equation implies S(2X^2)=2S-2X. Coefficient comparison and strong "
                + "induction force S to have coefficient function r. Thus S=R and B=A."),
            Node("hanna_conjecture", "The A389540 parity conjecture", HannaFormula(),
                "The inverse-coefficient recursion reduces R to X+X^2 modulo two. "
                + "Reducing R(A)=X therefore gives A+A^2=X over ZMod(2). Mathlib's "
                + "Frobenius identity identifies squaring with substitution of X^2. "
                + "At index one the coefficient is odd; at every larger positive even "
                + "index its parity equals the parity at half the index, and at every "
                + "larger odd index it is even. Strong induction gives precisely the "
                + "powers of two.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a389540-half-scaled-reflection-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a389540-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula R() => F.Id("R");
    private static Formula A() => F.Id("A");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) => Seq(
        Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp, yes, Sp,
        Named("else"), Sp, no);
    private static Formula Equation(Formula series) => Equal(Mul(D(2), Power(series, D(2))),
        Call("subst", series, Parenthesized(Subtract(Mul(D(2), X()), Mul(D(2), series)))));

    private static Formula InverseCoefficientFormula()
    {
        Formula n = F.Id("n");
        Formula half = Call("div", n, D(2));
        Formula multiplier = Power(D(2), Call("subNat", half, D(1)));
        Formula value = Conditional(Equal(n, D(0)), D(0),
            Conditional(Equal(n, D(1)), D(1),
                Conditional(Seq(D(2), Sp, Mid, Sp, n), Mul(multiplier, Call("r", half)), D(0))));
        return Disp(Seq(Bound("n", Naturals()), Equal(Call("r", n), value)));
    }

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()),
            Equal(Call("a", n), Call("coeff", n, Call("inv", R())))));
    }

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(0)), Conjunction(
            Equal(Call("coeff", D(1), A()), D(1)), Equation(A()))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Implication(Equal(Call("coeff", D(1), b), D(1)),
                    Implication(Equation(b), Equal(b, A()))))));
    }

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula support = Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Equal(n, Power(D(2), k)));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Le, Sp, n),
                Parenthesized(Seq(Call("Odd", Call("a", n)), Sp, Iff, Sp,
                    Parenthesized(support))))));
    }
}
