using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class PrimePowerShiftLogDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a393867");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nth prime divides the nth logarithmic-derivative term of OEIS A393866 for n greater than one.",
        H("Prime-Power Coefficient Equations and OEIS A393867"),
        Blocks(
            Paragraph(Text("The literature note hanna2026a393867 records Hanna's defining "
                + "equations for A393866 and the divisibility conjecture in A393867. Here F "
                + "denotes generatingSeries and L denotes logDerivative, both formal power "
                + "series over the integers. All indices and exponents are natural numbers; "
                + "subtraction in an index is natural subtraction. Coefficients and "
                + "divisibility are over the integers, with natural primes cast to integers.")),
            Paragraph(Text("The notation C embeds an integer as a constant series. The "
                + "operator derivative is the formal derivative over the integers, and "
                + "invOfUnit(F,1) is the formal inverse with constant coefficient one. "
                + "The operator div is integer division; every division used by the "
                + "coefficient construction is exact.")),
            Node("prime", "The one-based prime index", PrimeFormula(),
                "Mathlib's nth operator uses a zero-based index, so prime(n) is "
                + "Nat.nth Nat.Prime (n-1). The subtraction convention also defines prime(0).",
                DescribeRole.Definition),
            Node("lt_prime", "The prime exceeds its positive index", PrimeBoundFormula(),
                "Mathlib's bound k+2 <= Nat.nth Nat.Prime k, with k=n-1, gives the strict inequality."),
            Node("a", "The integral coefficient construction", CoefficientDefinitionFormula(),
                "Write P(k) for the private approximation(k). Starting from P(0)=1, "
                + "the displayed correction changes only degree k+1. In the binomial "
                + "expansion of B^p=(1+(B-1))^p, the interior binomial coefficients are "
                + "divisible by p and the pth power of B-1 has no coefficient below p. "
                + "This proves exact divisibility of the correction numerator. Later "
                + "approximations preserve every earlier coefficient.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series", Disp(Equal(Generating(), Call("mk", Named("a")))),
                "The series F is mk(a), the formal integer series with coefficient a(n) at degree n.",
                DescribeRole.Definition),
            Node("generating_equation", "The complete defining equations", GeneratingEquationFormula(),
                "If two unit-constant series agree below degree n, the difference of "
                + "their nth coefficients after taking the pth power is p times their "
                + "original nth-coefficient difference. Factoring the difference of "
                + "powers proves this identity. The exact correction therefore enforces "
                + "the nth equation; coefficient stability transfers it to F."),
            Node("generating_unique", "Uniqueness among integer series", UniqueFormula(),
                "Strong induction compares B and F below each degree n. Their defining "
                + "equations and the difference-of-powers coefficient identity imply "
                + "prime(n) times the coefficient difference is zero. Cancellation "
                + "of this nonzero integer proves equality at degree n."),
            Node("prime_dvd_coeff_pow", "Low coefficients of a prime power", PrimePowerFormula(),
                "Apply the binomial divisibility argument to F itself. The bound "
                + "1 <= j < prime(n) excludes both exceptional binomial terms."),
            Node("logDerivative", "The logarithmic derivative", LogDefinitionFormula(),
                "Since F has constant coefficient one, multiplication by its formal "
                + "unit inverse defines L=F'/F over the integers.", DescribeRole.Definition),
            Node("a393867", "The sequence indexing", SequenceFormula(),
                "A393867 starts at index one: its nth term is the coefficient of "
                + "degree n-1 in L. Natural subtraction also specifies the value at zero.",
                DescribeRole.Definition),
            Node("log_derivative_identity", "Differentiating every power", DerivativeFormula(),
                "The formal power rule and L times F equals F' give the displayed "
                + "identity, including exponent zero."),
            Node("hanna_conjecture", "Hanna's divisibility conjecture", ConjectureFormula(),
                "Let p=prime(n) and h(j) be the coefficient of degree j in F^p. "
                + "Coefficient extraction from the power rule, followed by h(n)=p h(n-1) "
                + "and cancellation of p, gives n h(n-1)=[x^(n-1)](L F^p). "
                + "For n>1, the left side is divisible by p. In the convolution on "
                + "the right, every term except [x^(n-1)]L times h(0) has a positive "
                + "coefficient index below p in F^p and is divisible by p. Since "
                + "h(0)=1, the remaining term proves the conjecture.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a393867-prime-power-shift-log-derivative"),
                    ResolutionKind.Proved)),
            Node("printed_formula_false", "The shifted printed formula is false", PrintedFormula(),
                "This companion concerns formula (2) of A393866, whose printed "
                + "coefficient index is n instead of n-1. The first three defining "
                + "equations give coefficients 1, 2, and 10 for F. Coefficient "
                + "extraction from L F=F' then gives [x^2]L=25, which is not "
                + "divisible by prime(2)=3. The separate oddness conjecture is not addressed."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a393867-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula J() => F.Id("j");
    private static Formula Generating() => F.Id("F");
    private static Formula Log() => F.Id("L");
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
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Positive(Formula n) => Seq(D(1), Sp, Le, Sp, n);
    private static Formula Coefficient(Formula n, Formula series) => Call("coeff", n, series);
    private static Formula Constant(Formula series) => Call("constantCoeff", series);
    private static Formula Prime(Formula n) => Call("prime", n);
    private static Formula Approx(Formula n) => Call("P", n);

    private static Formula PrimeFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Prime(N()), Call("nth", Named("Prime"), Subtract(N(), D(1))))));

    private static Formula PrimeBoundFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Positive(N()), Seq(N(), Sp, Lt, Sp, Prime(N())))));

    private static Formula CoefficientDefinitionFormula()
    {
        Formula next = Add(K(), D(1));
        Formula powered = Power(Approx(K()), Prime(next));
        Formula numerator = Subtract(Mul(Prime(next), Coefficient(Subtract(next, D(1)), powered)),
            Coefficient(next, powered));
        Formula correction = Call("div", Parenthesized(numerator), Prime(next));
        return Disp(new Formula.Aligned([
            Seq(Bound("n", Naturals()), Equal(Call("a", N()), Coefficient(N(), Approx(N())))),
            Equal(Approx(D(0)), D(1)),
            Seq(Bound("k", Naturals()), Equal(Approx(next), Add(Approx(K()),
                Mul(Call("C", correction), Power(X(), next)))))
        ]));
    }

    private static Formula EquationFamily(Formula series) => Seq(Bound("n", Naturals()),
        Implication(Positive(N()), Equal(Coefficient(N(), Power(series, Prime(N()))),
            Mul(Prime(N()), Coefficient(Subtract(N(), D(1)), Power(series, Prime(N())))))));

    private static Formula GeneratingEquationFormula() => Disp(Conjunction(
        Equal(Constant(Generating()), D(1)), EquationFamily(Generating())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()), Implication(Equal(Constant(b), D(1)),
            Implication(EquationFamily(b), Equal(b, Generating())))));
    }

    private static Formula PrimePowerFormula() => Disp(Seq(Bound("n", Naturals()),
        Bound("j", Naturals()), Implication(Positive(J()),
            Implication(Seq(J(), Sp, Lt, Sp, Prime(N())),
                Divides(Prime(N()), Coefficient(J(), Power(Generating(), Prime(N()))))))));

    private static Formula LogDefinitionFormula() => Disp(Equal(Log(),
        Mul(Call("derivative", Integers(), Generating()), Call("invOfUnit", Generating(), D(1)))));

    private static Formula SequenceFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a393867", N()), Coefficient(Subtract(N(), D(1)), Log()))));

    private static Formula DerivativeFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Mul(X(), Call("derivative", Integers(), Power(Generating(), N()))),
            Mul(Mul(Call("C", N()), Parenthesized(Mul(X(), Log()))), Power(Generating(), N())))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()), Divides(Prime(N()), Call("a393867", N())))));

    private static Formula PrintedFormula() => Disp(Seq(Neg, Sp,
        Parenthesized(Seq(Bound("n", Naturals()), Implication(Seq(D(1), Sp, Lt, Sp, N()),
            Divides(Prime(N()), Coefficient(N(), Log())))))));
}
