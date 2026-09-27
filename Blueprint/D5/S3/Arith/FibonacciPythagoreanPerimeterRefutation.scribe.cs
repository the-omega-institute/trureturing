using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class FibonacciPythagoreanPerimeterRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/huber2023a134492");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Fibonacci number at an index that is not a multiple of six is the perimeter of a "
            + "Pythagorean triangle, so the conjectured characterisation fails.",
        H("Fibonacci Numbers That Are Pythagorean Perimeters"),
        Blocks(
            Node("pythagorean-perimeter", "Being a Pythagorean perimeter", "IsPythPerimeter",
                PerimeterFormula(),
                "The source speaks of a number being the sum of the three numbers of a "
                    + "Pythagorean triple. The three numbers are the two legs and the "
                    + "hypotenuse, so their sum is the perimeter of the corresponding triangle. "
                    + "No qualifier appears in the source, so the triples range over all triples "
                    + "of positive integers satisfying the relation, primitive or not.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjectured-characterisation", "The conjectured characterisation", "claim",
                ClaimFormula(),
                "The comment on the sequence of Fibonacci numbers at indices divisible by six "
                    + "reads verbatim: \"For n at least two, the terms of this sequence are "
                    + "exactly those Fibonacci numbers which are the sum of the three numbers of "
                    + "a Pythagorean triple (checked up to F of eighty).\" Written out, the "
                    + "assertion is that a Fibonacci number is such a sum precisely when it is "
                    + "the value of the sequence at some index at least two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("characterisation-refuted", "The characterisation fails", "result",
                ResultFormula(),
                "Take the Fibonacci number at index forty-five, which is one billion one hundred "
                    + "thirty-four million nine hundred three thousand one hundred seventy. The "
                    + "three numbers three hundred forty-four million one hundred ninety-one "
                    + "thousand nine hundred forty-five, three hundred twenty million four "
                    + "hundred forty-three thousand two hundred forty-eight and four hundred "
                    + "seventy million two hundred sixty-seven thousand nine hundred seventy-seven "
                    + "satisfy the Pythagorean relation and add up to it, so it is a perimeter. "
                    + "It is not a term of the sequence: the terms jump from the Fibonacci number "
                    + "at index forty-two to the one at index forty-eight, and the Fibonacci "
                    + "function is monotone, so no index at least two can produce it. The witness "
                    + "was found by writing a perimeter as twice a product of three factors, two "
                    + "of them coprime with the larger between the smaller and its double and "
                    + "odd, and then testing the Fibonacci numbers at indices divisible by three; "
                    + "at the other indices they are odd and a perimeter is even. Index forty-five "
                    + "is the smallest failure, and it lies inside the range the comment reports "
                    + "having checked.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fibonacci-pythagorean-perimeter-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Fib(Formula argument) => Call("fib", argument);

    private static Formula Sq(Formula x) => new Formula.Power(x, D(2));

    private static Formula PerimeterFormula()
    {
        var N = F.Id("N");
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var body = And(Less(D(0), a),
            And(Less(D(0), b),
                And(Less(D(0), c),
                    And(Equal(Add(Sq(a), Sq(b)), Sq(c)),
                        Equal(Add(Add(a, b), c), N)))));
        return Disp(Universal("N", Naturals(),
            Iff(Call("IsPythPerimeter", N),
                Exists("a", Naturals(), Exists("b", Naturals(), Exists("c", Naturals(), body))))));
    }

    private static Formula ClaimFormula()
    {
        var N = F.Id("N");
        var k = F.Id("k");
        var n = F.Id("n");
        var isFib = Exists("k", Naturals(), Equal(Fib(k), N));
        var rhs = Exists("n", Naturals(),
            And(LessEqual(D(2), n), Equal(Fib(Multiply(D(6), n)), N)));
        var body = Universal("N", Naturals(),
            Implies(isFib, Iff(Call("IsPythPerimeter", N), rhs)));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(Parenthesized(F.Id("claim"))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
