using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class RicciLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FluidDynamics/lichtenfelz2026zeitlin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Averaged Ricci curvature of the Zeitlin metric.",
        H("Zeitlin Ricci Curvature Limit"),
        Blocks(
            Paragraph(Text("Nat and Real denote natural and real numbers. real is the natural-to-real or rational-to-real cast. Natural subtraction is truncated at zero. range(n) is {0,...,n-1}; the shifted indices i+1 and j+1 therefore traverse 1,...,N-1. div is field division and ite selects a value according to its condition. W is the six-j symbol with equal bottom-row spins (N-1)/2; casimir(k)=k(k+1). harmonic(l) is rational and is cast to Real.")),
            Node("rPlus", "Positive contribution", Contribution(false),
                "Equation (2.4) gives the positive contribution. The prefactor N divided by 4/(N squared minus 1) is N divided by the squared quantization parameter. Only odd total top-row parity contributes.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rMinus", "Negative contribution", Contribution(true),
                "Equation (2.4) gives the negative contribution, weighted by the squared difference of the two summation Casimirs.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rTilde", "Averaged Ricci curvature",
                Disp(All("l", N("Nat"), All("N", N("Nat"), Eq(
                    Typed(Call("rTilde", N("l"), N("N")), N("Real")),
                    Div(Sub(Call("rPlus", N("l"), N("N")), Call("rMinus", N("l"), N("N"))), Denominator()))))),
                "Equation (2.15) divides the Ricci curvature by the dimension N squared minus 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The Ricci limit conjecture",
                Disp(Eq(Typed(N("claim"), N("Prop")), ClaimBody())),
                "Conjecture 2 in section 2.2 asserts that for every fixed label at least two the averaged curvature tends to minus one half of the harmonic number minus one, and is negative for all sufficiently large dimensions. The threshold may depend on the fixed label.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fixed_labels_odd_tendsto_zero", "Decay at fixed odd labels",
                Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), Implies(
                    Call("Odd", Add(Add(N("a"), N("b")), N("c"))),
                    Limit(Mul(Real(N("N")), Square(Call("W", N("N"), N("a"), N("b"), N("c")))), D(0))))))),
                "For a fixed odd-parity triple, N times the squared six-j symbol tends to zero. The odd weighted Casimir moment tends to zero by the terminating Racah expansion. Its nonnegative summands bound each fixed positive label; a zero label has inadmissible odd parity and contributes zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-riccilimit-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => Call("div", a, b);
    private static Formula Square(Formula a) => new Formula.Power(Parenthesized(a), D(2));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Real(Formula a) => Call("real", a);
    private static Formula Casimir(Formula a) => Call("casimir", a);
    private static Formula Dimension(Formula a) => Add(Mul(D(2), Real(a)), D(1));
    private static Formula Denominator() => Sub(Square(Real(N("N"))), D(1));
    private static Formula SumOver(string name, Formula body) => Seq(Sum, Underscore,
        Grp(Seq(N(name), InMacro, Call("range", Sub(N("N"), D(1))))), Parenthesized(body));
    private static Formula Limit(Formula body, Formula value) => Call("Tendsto",
        Parenthesized(Seq(Typed(N("N"), N("Nat")), Mapsto, body)), N("atTop"), Call("nhds", value));
    private static Formula ClaimBody() => All("l", N("Nat"), Implies(Le(D(2), N("l")), And(
        Limit(Call("rTilde", N("l"), N("N")), Div(new Formula.Negate(Sub(Real(Call("harmonic", N("l"))), D(1))), D(2))),
        Exists("N0", N("Nat"), All("N", N("Nat"), Implies(Le(N("N0"), N("N")), Lt(Call("rTilde", N("l"), N("N")), D(0))))))));

    private static Formula Contribution(bool negative)
    {
        Formula i = Add(N("i"), D(1));
        Formula j = Add(N("j"), D(1));
        Formula numerator = negative ? Square(Sub(Casimir(i), Casimir(j))) : Casimir(N("l"));
        Formula denominator = Mul(Casimir(i), Casimir(j));
        if (negative) denominator = Mul(denominator, Casimir(N("l")));
        Formula summand = Mul(Div(Mul(Mul(numerator, Dimension(i)), Dimension(j)), denominator),
            Square(Call("W", N("N"), N("l"), i, j)));
        return Disp(All("l", N("Nat"), All("N", N("Nat"), Eq(
            Typed(Call(negative ? "rMinus" : "rPlus", N("l"), N("N")), N("Real")),
            Mul(Div(Real(N("N")), Div(D(4), Denominator())),
                SumOver("i", SumOver("j", Call("ite", Call("Odd", Add(Add(i, j), N("l"))), summand, D(0)))))))));
    }
}
