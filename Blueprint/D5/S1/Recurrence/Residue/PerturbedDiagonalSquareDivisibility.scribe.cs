using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class PerturbedDiagonalSquareDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2023a365095");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's vanishing diagonal defines a unique integer series and implies square divisibility for every integer perturbation.",
        H("Perturbed Diagonal Square Divisibility"),
        Blocks(
            Paragraph(Text("The note hanna2023a365095 records the defining equation and "
                + "conjecture of OEIS A365095. Write A for generatingSeries and P(d) for "
                + "the integer-series approximation at depth d. The indices n and d are "
                + "natural numbers, while k is an arbitrary integer and B is an integer "
                + "power series. Subtraction in the index n-1 is natural subtraction; "
                + "subtraction in parameters is integer subtraction, with intCast marking "
                + "the conversion from natural numbers.")),
            Paragraph(Text("The operator coeff extracts a coefficient, mk forms a series "
                + "from its coefficient function, and C embeds an integer as a constant "
                + "series. The symbols 1 and X denote the unit series and formal variable. "
                + "The expression invOfUnit(f,1) is the formal inverse when coeff(0,f)=1. "
                + "The operator ediv is integer division; each division in the update "
                + "below is proved exact. Divisibility in the conclusion is over the integers.")),
            Node("a", "The integral triangular construction", CoefficientDefinition(),
                "The degree-n residual is the coefficient of the (n+1)-st power of "
                + "invOfUnit(P(d),1)+C(intCast(n))*X*P(d). Differentiation proves that "
                + "n+1 divides this coefficient. If two normalized series agree below n, "
                + "their residuals differ by -(n+1) times their degree-n coefficient "
                + "difference. Thus the update extends agreement by one degree and "
                + "the approximations stabilize.", DescribeRole.Definition),
            Node("generatingSeries", "The normalized integer series",
                Disp(Equal(A(), Call("mk", F.Id("a")))),
                "The stabilized integer coefficient function a defines A.", DescribeRole.Definition),
            Node("generating_equation", "The defining vanishing diagonal",
                Disp(Conjunction(Equal(Coefficient(D(0), A()), D(1)), Equation(A()))),
                "Stabilization gives a fixed point of the triangular update. Exact "
                + "division then forces every positive-degree residual to vanish. "
                + "Multiplying 1+C(t)*X*A^2 by invOfUnit(A,1) gives "
                + "invOfUnit(A,1)+C(t)*X*A. Taking the n-th power bridges the residual "
                + "to precisely the defining diagonal with t=n-1."),
            Node("generating_unique", "Uniqueness among normalized integer series", UniqueFormula(),
                "Any B satisfying the normalized vanishing diagonal is a fixed point "
                + "of the same exact integer update. The inverse-difference identity "
                + "and leading-power coefficient calculation show that the update "
                + "improves agreement by one degree. Induction identifies B with A."),
            Node("perturbedDiagonal", "The integer-parameter diagonal",
                Disp(Seq(Bound("k", Integers()), Bound("n", Naturals()),
                    Equal(Call("perturbedDiagonal", K(), N()),
                        Diagonal(A(), Subtract(Mul(K(), IntCast(N())), D(1)), N())))),
                "This is the coefficient extraction in formula (2), using the n-th "
                + "power of the formal unit inverse for division by A(x)^n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hanna_conjecture", "Square divisibility for every integer k",
                Disp(Seq(Bound("k", Integers()), Bound("n", Naturals()),
                    Implication(Seq(D(0), Sp, Lt, Sp, N()),
                        Divides(Power(IntCast(N()), D(2)), Call("perturbedDiagonal", K(), N()))))),
                "Replacing n-1 by k*n-1 adds n*C(k-1)*X*A^2 to the base of the "
                + "n-th power. Mathlib's dvd_sub_pow_of_dvd_sub gives divisibility "
                + "of the power difference by n^2. Multiplication by invOfUnit(A,1)^n "
                + "and coefficient extraction preserve it. For n>1 the defining "
                + "diagonal is zero; for n=1 the divisor is one. No sign restriction "
                + "is imposed on k.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a365095-perturbed-diagonal-square-divisibility"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("perturbed-diagonal-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula A() => F.Id("A");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula IntCast(Formula n) => Call("intCast", n);
    private static Formula Root(Formula f, Formula t) =>
        Add(Call("invOfUnit", f, D(1)), Mul(Mul(Call("C", t), F.Id("X")), f));
    private static Formula Diagonal(Formula f, Formula t, Formula n) =>
        Coefficient(Subtract(n, D(1)),
            Mul(Power(Add(D(1), Mul(Mul(Call("C", t), F.Id("X")), Power(f, D(2)))), n),
                Power(Call("invOfUnit", f, D(1)), n)));
    private static Formula Equation(Formula f) => Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()),
            Equal(Diagonal(f, Subtract(IntCast(N()), D(1)), N()), D(0))));

    private static Formula CoefficientDefinition()
    {
        var d = F.Id("d");
        var approximation = Call("P", d);
        var residual = Coefficient(N(), Power(Root(approximation, IntCast(N())), Add(N(), D(1))));
        var next = Seq(Named("if"), Sp, Parenthesized(Equal(N(), D(0))),
            Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp,
            Add(Coefficient(N(), approximation), Call("ediv", residual, Add(IntCast(N()), D(1)))));
        return Disp(new Formula.Aligned([
            Equal(Call("P", D(0)), D(1)),
            Seq(Bound("d", Naturals()),
                Equal(Call("P", Add(d, D(1))), Call("mk", Lambda("n", next)))),
            Seq(Bound("n", Naturals()),
                Equal(Call("a", N()), Coefficient(N(), Call("P", Add(N(), D(1))))))
        ]));
    }

    private static Formula UniqueFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("B", Call("PowerSeries", Integers())),
            Implication(Equal(Coefficient(D(0), b), D(1)),
                Implication(Equation(b), Equal(b, A())))));
    }
}
