using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ShrunkenGrassmannianConjectureSixteenRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CayleyGrowth/chervov2026cayleypy4");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjecture 16 of CayleyPy-4 is false under both readings of the diameter: with rotations of four consecutive letters on words with two zeros and three ones, the word 11010 is three moves from 00111, one more than the conjectured formula.",
        H("Conjecture 16 of CayleyPy-4 fails at k = 4, L = 2, N = 5"),
        Blocks(
            Node("four", "The k = 4 formula", FourFormula(),
                "The k = 4 clause of Conjecture 16: L/3 times (N - L) when 3 divides L, and the floor of (L(N - L) + 2)/3 otherwise.",
                "formulaFour", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("five", "The k = 5 formula", FiveFormula(),
                "The k = 5 clause of Conjecture 16: the floor of (LN + 2)/4, minus twice the floor of L^2/8, minus 1 when both L and N are congruent to 2 modulo 4.",
                "formulaFive", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conj", "Conjecture 16 under a reading of the diameter", ConjFormula(),
                "The three clauses of Conjecture 16 for a reading D(k, L, N) of the diameter: k = 3 from L >= 2, k = 4 from L >= 2, both for N > k, and k = 5 once L and N - L exceed some constant.",
                "conjSixteen", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture under either reading", ClaimFormula(),
                "The conjecture holds for the largest distance from the central state or for the largest distance between two vertices.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "Every word reached from x within m moves lies in the list obtained from [x] by m times appending all rotations of all listed words. For k = 4 and the words of length 5 the kernel evaluates this list for m = 2 from 00111 and finds that it does not contain 11010, which has two zeros and three ones. If either reading gave the value 2 at L = 2, N = 5, the least element of the defining set would be 2, so 11010 would be reached from 00111, which is also a vertex, within two moves. The formula gives the floor of 8/3, which is 2, because 3 does not divide 2.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chervov-2026-cayleypy4-conjecture-sixteen-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("cayley16-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula FloorOver(Formula numerator, Formula denominator) =>
        new Formula.Floor(new Formula.Fraction(numerator, denominator));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);

    private static Formula FourFormula()
    {
        Formula l = F.Id("L"), n = F.Id("N");
        Formula value = IfThenElse(Divides(D(3), l),
            Times(FloorOver(l, D(3)), Parenthesized(Subtract(n, l))),
            FloorOver(Add(Times(l, Parenthesized(Subtract(n, l))), D(2)), D(3)));
        return Disp(Equal(Call("formulaFour", l, n), value));
    }

    private static Formula FiveFormula()
    {
        Formula l = F.Id("L"), n = F.Id("N");
        Formula condition = And(Equal(new Formula.Modulo(l, D(4)), D(2)), Equal(new Formula.Modulo(n, D(4)), D(2)));
        Formula value = Subtract(Subtract(FloorOver(Add(Times(l, n), D(2)), D(4)),
            Times(D(2), FloorOver(new Formula.Power(l, D(2)), D(8)))),
            Parenthesized(IfThenElse(condition, D(1), D(0))));
        return Disp(Equal(Call("formulaFive", l, n), value));
    }

    private static Formula ConjFormula()
    {
        Formula l = F.Id("L"), n = F.Id("N"), c = F.Id("C");
        Formula d = F.Id("D");
        Formula three = All("L", Naturals(), All("N", Naturals(), Implies(
            And(And(AtMost(D(2), l), AtMost(l, n)), Less(D(3), n)),
            Equal(new Formula.Apply(d, [D(3), l, n]), FloorOver(Add(Times(l, Parenthesized(Subtract(n, l))), D(1)), D(2))))));
        Formula four = All("L", Naturals(), All("N", Naturals(), Implies(
            And(And(AtMost(D(2), l), AtMost(l, n)), Less(D(4), n)),
            Equal(new Formula.Apply(d, [D(4), l, n]), Call("formulaFour", l, n)))));
        Formula five = Ex("C", Naturals(), All("L", Naturals(), All("N", Naturals(), Implies(
            And(AtMost(c, l), AtMost(c, Subtract(n, l))),
            Equal(new Formula.Apply(d, [D(5), l, n]), Call("formulaFive", l, n))))));
        return Disp(Iff(Call("conjSixteen", d),
            And(And(Parenthesized(three), Parenthesized(four)), Parenthesized(five))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"),
        Or(Call("conjSixteen", F.Id("ecc")), Call("conjSixteen", F.Id("diam")))));
}
