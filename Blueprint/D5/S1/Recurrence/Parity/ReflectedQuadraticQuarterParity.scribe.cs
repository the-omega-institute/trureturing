using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class ReflectedQuadraticQuarterParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2024a369083");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer coefficients of OEIS A369083 have the conjectured binomial parity.",
        H("Reflected Quadratic Quarter Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2024a369083 defines A by "
                + "A(x)=1+x*(5*A(x)^2-A(-x)^2)/4 and conjectures the parity of "
                + "binomial(4*n+3,n) for every natural index n, including zero. "
                + "The equation below clears the denominator four over the integers.")),
            Paragraph(Text("All indices are natural numbers and all coefficients are integers. "
                + "A denotes generatingSeries; P(n) denotes its private approximations. "
                + "The operator coeff extracts a coefficient, mk constructs a series, "
                + "Even is the even-index predicate, and ite selects its second argument "
                + "when its first argument holds and its third otherwise. The operator "
                + "ediv is integer Euclidean division; mod is integer remainder. "
                + "The series rescale(-1,B) is B(-X). The map pi sends integers to "
                + "ZMod(2), and map(pi,B) applies it coefficientwise. G denotes the "
                + "integer generatingSeries of AbsoluteReciprocalCubeParity: it has "
                + "constant coefficient one and satisfies "
                + "G=1+X*absSeries(invOfUnit(G,1))^3, as recorded in hanna2024a369083.")),
            Node("a", "The integer coefficient sequence", SequenceFormula(),
                "The update uses the coefficient of P(n)^2 at the preceding index. "
                + "At odd indices of that square, reduction modulo two and Frobenius "
                + "show divisibility by two. Each update increases coefficient agreement "
                + "by one degree, so the diagonal coefficients define an integer solution.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Equal(A(), Call("mk", F.Id("a")))),
                "The generating series has coefficient function a.", DescribeRole.Definition),
            Node("generating_equation", "The normalized OEIS equation",
                Disp(Conjunction(Equal(Call("constantCoeff", A()), D(1)), Equation(A()))),
                "Coefficient stabilization gives the fixed point. Even degrees of the "
                + "square contribute directly; odd degrees contribute three times their "
                + "exact half. These are precisely the coefficients of the equation "
                + "with its denominator cleared."),
            Node("generating_unique", "Uniqueness over the integers", UniqueFormula(),
                "Cancelling four shows that any solution is fixed by the coefficient "
                + "update. Induction on the degree of agreement identifies it with A."),
            Node("reflection_linear", "Eliminating the reflected series",
                Disp(Equal(Reflect(A()), Subtract(Subtract(Mul(D(5), A()), D(4)),
                    Mul(Mul(D(6), X()), Power(A(), D(2)))))),
                "Rescaling the equation by minus one gives its reflected counterpart. "
                + "Subtracting five times the original equation cancels the reflected "
                + "square; cancelling four gives this linear expression."),
            Node("quartic_equation", "The quartic equation", QuarticFormula(),
                "Substituting the reflected expression into the original equation "
                + "and cancelling four gives the displayed quartic."),
            Node("choose_shift", "Adjacent binomial coefficients", ChooseFormula(),
                "Mathlib's adjacent-binomial identity gives equality after multiplication "
                + "by n+1. Since 4*n+3-n=3*(n+1), cancellation gives the factor three."),
            Node("mod_two_identity", "Identification with the reciprocal-cube series",
                Disp(Equal(Add(D(1), Mul(X(), Reduce(A()))), Reduce(G()))),
                "Writing F=map(pi,A), the quartic reduces to F*(1+X*F)^3=1. "
                + "Consequently H=1+X*F satisfies H^4-H^3=X. Absolute values are "
                + "invisible modulo two, so map(pi,G) satisfies the same equation. "
                + "The difference factors through a series of constant coefficient "
                + "one, whose invertibility proves equality."),
            Node("hanna_conjecture", "Hanna's binomial parity conjecture", HannaFormula(),
                "The coefficient of degree n+1 in G modulo two is "
                + "binomial(4*n+3,n+1). The series identity identifies it with a(n). "
                + "The adjacent-binomial identity changes it to three times "
                + "binomial(4*n+3,n), which has the same parity.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a369083-reflected-quadratic-quarter-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a369083-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula A() => F.Id("A");
    private static Formula G() => F.Id("G");
    private static Formula X() => F.Id("X");
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
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Reflect(Formula series) => Call("rescale", Seq(Minus, D(1)), series);
    private static Formula Reduce(Formula series) => Call("map", F.Id("pi"), series);
    private static Formula Equation(Formula series) => Equal(
        Mul(D(4), Parenthesized(Subtract(series, D(1)))),
        Mul(X(), Parenthesized(Subtract(Mul(D(5), Power(series, D(2))),
            Power(Reflect(series), D(2))))));

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula p = Call("P", n);
        Formula next = Call("P", Add(n, D(1)));
        Formula s = Call("coeff", k, Power(p, D(2)));
        return Disp(new Formula.Aligned([
            Equal(Call("P", D(0)), D(1)),
            Seq(Bound("n", Naturals()), Equal(Call("coeff", D(0), next), D(1))),
            Seq(Bound("n", Naturals()), Bound("k", Naturals()),
                Equal(Call("coeff", Add(k, D(1)), next),
                    Call("ite", Call("Even", k), s, Mul(D(3), Call("ediv", s, D(2)))))),
            Seq(Bound("n", Naturals()), Equal(Call("a", n), Call("coeff", n, next)))
        ]));
    }

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(Equation(b), Equal(b, A())))));
    }

    private static Formula QuarticFormula()
    {
        Formula linear = Mul(Parenthesized(Subtract(Mul(D(1, 0), X()), D(1))), A());
        Formula quadratic = Mul(Parenthesized(Add(Mul(D(5), X()),
            Mul(D(1, 2), Power(X(), D(2))))), Power(A(), D(2)));
        Formula cubic = Mul(Mul(D(1, 5), Power(X(), D(2))), Power(A(), D(3)));
        Formula quartic = Mul(Mul(D(9), Power(X(), D(3))), Power(A(), D(4)));
        return Disp(Equal(Subtract(Add(Subtract(Add(Subtract(D(1), Mul(D(4), X())),
            linear), quadratic), cubic), quartic), D(0)));
    }

    private static Formula ChooseFormula()
    {
        Formula n = F.Id("n");
        Formula top = Add(Mul(D(4), n), D(3));
        return Disp(Seq(Bound("n", Naturals()), Equal(Call("choose", top, Add(n, D(1))),
            Mul(D(3), Call("choose", top, n)))));
    }

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()), Equal(new Formula.Modulo(Call("a", n), D(2)),
            new Formula.Modulo(Call("choose", Add(Mul(D(4), n), D(3)), n), D(2)))));
    }
}
