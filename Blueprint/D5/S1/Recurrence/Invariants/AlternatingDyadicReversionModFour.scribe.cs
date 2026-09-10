using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AlternatingDyadicReversionModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2025a389537");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A389537 satisfy Hanna's mod-four classification.",
        H("Alternating Dyadic Reversion Modulo Four"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a389537 defines A by "
                + "A(A(x)-x)=A(x)^2. Its conjecture says that for n greater than two, "
                + "a(n) is congruent to two modulo four exactly at indices 3 times "
                + "a power of two, and is divisible by four at every other such index.")),
            Paragraph(Text("All indices are natural numbers. The coefficient functions "
                + "r and a take integer values. R denotes inverseSeries and A denotes "
                + "generatingSeries in PowerSeries(Z), with indeterminate X. The local "
                + "coefficient function r is specified together with R below. The operator "
                + "mk constructs a series from its coefficient function; coeff(n,B) "
                + "extracts a coefficient; subst(B,C) substitutes C into B. The notation "
                + "inv(R) is Mathlib's substInvOfIsUnit applied to the proved unit linear "
                + "coefficient of R. The operator div is natural-number division on the index, "
                + "and mod is the natural-number remainder.")),
            Node("inverseSeries", "The alternating dyadic inverse", InverseFormula(),
                "The recursion sets r(0)=0 and r(1)=1. At every other even index it "
                + "negates the coefficient at half the index; at every other odd index "
                + "it vanishes. Thus R is the alternating dyadic series, with coefficient "
                + "(-1)^j at degree 2^j and zero elsewhere.", DescribeRole.Definition),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "The coefficient a(n) is extracted from the integral compositional "
                + "inverse of R.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Equal(A(), Call("mk", F.Id("a")))),
                "The series A has coefficient function a and is the compositional "
                + "inverse of R in both orders.", DescribeRole.Definition),
            Node("inverse_equation", "The dyadic reversion identity",
                Disp(Equal(Add(R(), Call("subst", R(), Power(X(), D(2)))), X())),
                "Coefficient comparison reduces every positive even degree to half "
                + "that degree. The two coefficients have opposite signs and cancel; "
                + "the linear coefficient remains one."),
            Node("generating_equation", "The OEIS equation and normalization", EquationFormula(),
                "Substituting A into R+R(X^2)=X and using R(A)=X gives "
                + "R(A^2)=A-X. Composing with A gives A(A-X)=A^2. Integral "
                + "compositional reversion supplies the two normalization conditions."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "For any normalized integer solution B, its compositional inverse S "
                + "satisfies S+S(X^2)=X. Strong induction on the coefficient index "
                + "shows that S=R, since the only earlier index required is its half. "
                + "The inverse identities then give B=A."),
            Node("hanna_conjecture", "Hanna's coefficient conjecture", HannaFormula(),
                "Work over ZMod(4), and let D have coefficient one exactly at indices "
                + "3 times a power of two. Halving these indices gives D=X^3+D(X^2). "
                + "Squaring erases a perturbation 2T, so the inverse equation gives "
                + "R(S+2T)=R(S)+2T for zero-constant S and T. Set U=X+X^2. Since "
                + "U^2=U(X^2)+2X^3, H=R(U) satisfies H+H(X^2)=U-2X^3. "
                + "The series X+2D satisfies the same equation and has the same "
                + "constant coefficient, so coefficient halving proves H=X+2D. "
                + "Consequently R(U+2D)=X, and compositional inversion gives "
                + "A=U+2D modulo four. Extracting every coefficient above degree "
                + "two proves both biconditionals.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a389537-alternating-dyadic-reversion-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a389537-" + name.Replace('_', '-').ToLowerInvariant()),
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
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
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
    private static Formula Equation(Formula series) => Equal(
        Call("subst", series, Parenthesized(Subtract(series, X()))), Power(series, D(2)));

    private static Formula InverseFormula()
    {
        Formula n = F.Id("n");
        Formula value = Conditional(Equal(n, D(0)), D(0),
            Conditional(Equal(n, D(1)), D(1),
                Conditional(Seq(D(2), Sp, Mid, Sp, n),
                    Seq(Minus, Call("r", Call("div", n, D(2)))), D(0))));
        return Disp(new Formula.Aligned([
            Equal(R(), Call("mk", F.Id("r"))),
            Seq(Bound("n", Naturals()), Equal(Call("r", n), value))
        ]));
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
            Equal(n, Mul(D(3), Power(D(2), k))));
        Formula remainder = new Formula.Modulo(Call("a", n), D(4));
        Formula two = Seq(Equal(remainder, D(2)), Sp, Iff, Sp, Parenthesized(support));
        Formula zero = Seq(Equal(remainder, D(0)), Sp, Iff, Sp,
            Neg, Sp, Parenthesized(support));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(2), Sp, Lt, Sp, n),
                Parenthesized(Conjunction(two, zero)))));
    }
}
