using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class GerasimovLeastEvenDivisorCountPowerOfTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/gerasimov2011a187941");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal offset-zero form of Gerasimov's A187941 conjecture and its positive-index form.",
        H("Least Numbers with a Prescribed Even-Divisor Count"),
        Blocks(
            Node("E", "Even-divisor count", EvenDivisorCountFormula(),
                "E(m) is the cardinality of the even members of the natural divisor finset of m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "Least number with n even divisors", SequenceFormula(),
                "The natural infimum selects the least positive number with the prescribed "
                    + "even-divisor count. The set is nonempty for every n; by convention, "
                    + "sInf of the empty set is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The literal offset-zero conjecture", ClaimFormula(),
                "The entry has offset zero, so this literal universal statement includes n = 0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The offset-zero conjecture is false", ResultFormula(),
                "At n = 0, the least number with no even divisors is a(0) = 1 = 2^0, "
                    + "while zero is neither prime nor equal to one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("gerasimov_a187941", "The positive-index implication", PositiveIndexFormula(),
                "For composite n = d times e, the multiplicative count "
                    + "E(2^d times 3^(e-1)) = d times e gives a smaller witness than 2^n. "
                    + "Thus equality with 2^n at a positive index forces n to be prime or one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("a187941-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula EvenDivisorCountFormula()
    {
        var m = F.Id("m");
        var filtered = Call("filter", F.Id("Even"), Call("divisors", m));
        return Disp(All("m", Equal(Call("E", m), Call("card", filtered))));
    }

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var conditions = And(Less(D(0), m), Equal(Call("E", m), n));
        var witnesses = Seq(OpenBrace, m, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            conditions, CloseBrace);
        return Disp(All("n", Equal(Call("a", n), Call("sInf", witnesses))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var conclusion = Or(Call("Prime", n), Equal(n, D(1)));
        var implication = Implies(Equal(Call("a", n), Power(D(2), n)), conclusion);
        return Disp(Iff(Parenthesized(F.Id("claim")), Parenthesized(All("n", implication))));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula PositiveIndexFormula()
    {
        var n = F.Id("n");
        var conclusion = Or(Call("Prime", n), Equal(n, D(1)));
        return Disp(All("n", Implies(
            LessOrEqual(D(1), n),
            Implies(Equal(Call("a", n), Power(D(2), n)), conclusion))));
    }

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula All(string name, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            Naturals(),
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
