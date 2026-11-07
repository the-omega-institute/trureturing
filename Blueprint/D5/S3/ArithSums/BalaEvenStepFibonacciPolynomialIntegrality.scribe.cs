using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class BalaEvenStepFibonacciPolynomialIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/bala2021a349272");
    private const string SourceSentence =
        "More generally, if F(n,x) denotes the n-th Fibonacci polynomial we conjecture that, for each n, the rational function Product_{k = 1..2*n+1} F(m*k,x) / Sum_{k = 1..2*n+1} F(m*k,x) is an integral polynomial.";
    private const string StepSentence =
        "Let m be an even positive integer. We conjecture that the sequence defined by b_m(n) = Product_{k = 1..2*n+1} Fibonacci(m*k) / Sum_{k = 1..2*n+1} Fibonacci(m*k) is integral. The formula given below proves the conjecture in the present case m = 2. The cases m = 4 and m = 6 of the conjecture can be proved in a similar manner.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive even Fibonacci-polynomial steps have integral odd product-sum quotients.",
        H("Bala's even-step Fibonacci-polynomial quotient"),
        Blocks(
            Paragraph(Text("OEIS A349272, COMMENT 1: " + StepSentence)),
            Paragraph(Text("OEIS A349272, COMMENT 2 (an unpaginated entry): " + SourceSentence)),
            Paragraph(Text(
                "The existing fibonacciRecurrencePolynomial has initial values 0 and 1 and recurrence "
                + "fibonacciRecurrencePolynomial(j+2) = X*fibonacciRecurrencePolynomial(j+1) + fibonacciRecurrencePolynomial(j). "
                + "The index n starts at zero, as in the entry's offset. Products and sums include both endpoints. "
                + "An integral polynomial has integer coefficients. The quotient is an equality in RatFunc Rat; "
                + "it makes no pointwise division assertion at a zero of the denominator.")),
            Node("numerator", "The odd product", ProductFormula(),
                "The product in COMMENT 2 runs over k from 1 through 2*n+1, at step m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("denominator", "The odd partial sum", SumFormula(),
                "The sum in COMMENT 2 uses precisely the same indices as the product.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The polynomial assertion", Disp(Iff(F.Id("claim"), ClaimBody())),
                "OEIS A349272, COMMENT 2 (unpaginated): " + SourceSentence
                + " COMMENT 1 supplies the positive even step m, encoded by 2 <= m and Even m. "
                + "Both m and n are natural numbers. The statement also requires a nonzero polynomial denominator. "
                + "The coefficient map Int.castRingHom Rat followed by algebraMap embeds each integer polynomial into rational functions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The quotient has integer coefficients", Disp(ClaimBody()),
                "Even m makes the m-th power of the Fibonacci companion matrix have determinant one. "
                + "Its trace t identifies the sampled polynomials as c*lucasU(t,1,k), where c is the m-th Fibonacci polynomial. "
                + "The odd partial sum factors as lucasU(t,1,n+1)*(lucasU(t,1,n+1)+lucasU(t,1,n)). "
                + "The doubling identity factors the last numerator term as a difference of squares. "
                + "For n>0, take the integer polynomial c^(2*n)*(lucasU(t,1,n+1)-lucasU(t,1,n)) "
                + "times the product of lucasU(t,1,k) over 1 <= k <= 2*n, excluding n+1. For n=0 take 1. "
                + "This gives denominator*H=numerator without cancellation, over every commutative ring. "
                + "The last summand has uniquely greatest degree and coefficient one for m>=2. "
                + "Thus the denominator is nonzero and the multiplication identity gives the rational-function equality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("bala-a349272-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ProductFormula() => Disp(All("m", Nat(), All("n", Nat(),
        Equal(Call("numerator", F.Id("m"), F.Id("n")), Range(F.Prod)))));
    private static Formula SumFormula() => Disp(All("m", Nat(), All("n", Nat(),
        Equal(Call("denominator", F.Id("m"), F.Id("n")), Range(F.Sum)))));
    private static Formula Range(Formula op)
    {
        var k = F.Id("k");
        var upper = Add(Mul(D(2), F.Id("n")), D(1));
        var indices = Seq(k, Sp, InMacro, Sp, App(Qualified("Finset", "Icc"), D(1), upper));
        return Seq(new Formula.Subscript(op, indices), Sp,
            Call("fibonacciRecurrencePolynomial", Mul(F.Id("m"), k)));
    }
    private static Formula ClaimBody()
    {
        var m = F.Id("m"); var n = F.Id("n"); var h = F.Id("H");
        var p = Call("numerator", m, n); var d = Call("denominator", m, n);
        var equality = Equal(new Formula.Fraction(Embed(p), Embed(d)), Embed(h));
        var conclusion = And(new Formula.Relation(d, FormulaRelationOperator.NotEqual, D(0)),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("H"), Poly(Ints()), equality));
        return All("m", Nat(), All("n", Nat(), Implies(
            new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, m),
            Implies(Call("Even", m), conclusion))));
    }
    private static Formula Embed(Formula p) => App(Call("algebraMap", Poly(Rats()), Call("RatFunc", Rats())),
        App(Qualified("Polynomial", "map"), App(Qualified("Int", "castRingHom"), Rats()), p));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Ints() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Rats() => new Formula.NamedConstant(FormulaIdentifier.Create("Rat"));
    private static Formula Poly(Formula r) => Call("Polynomial", r);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
