using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class BarkerBinaryGramRecurrenceRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/barker2018a181278");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The n = 4 term refutes Barker's published recurrence for OEIS A181278.",
        H("The OEIS A181278 Binary Gram-Row Recurrence"),
        Blocks(
            Node("a181278-count", "The A181278 counting function", A181278Formula(),
                "The range from zero through 2^n-1 lists every length-n binary row once, "
                    + "including rows with leading zeroes. The predicate countP counts ordered "
                    + "pairs p whose first row is smaller than the second. Parity is the "
                    + "remainder modulo two of the number of set bits below n, and dot is the "
                    + "corresponding common-set-bit count. The final strict inequality compares "
                    + "the two Gram rows lexicographically with their first entries as the high "
                    + "digits.",
                "a181278", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("barker-recurrence-claim", "Barker's published recurrence", ClaimFormula(),
                "The index is the OEIS index without a shift, so a181278(1)=0. The premise "
                    + "4<=n is exactly the published condition n>3. Moving the negative term "
                    + "to the left gives an equality of natural numbers that is equivalent "
                    + "after casting to the integers and introduces no extra nonnegativity "
                    + "hypothesis. Each displayed index subtraction is natural subtraction; "
                    + "under the premise, all three indices are positive.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("barker-recurrence-refuted", "The recurrence fails at n = 4", ResultFormula(),
                "The defining finite count gives a181278(1)=0, a181278(2)=3, "
                    + "a181278(3)=11, and a181278(4)=48. Specializing the claim at n=4 would "
                    + "therefore assert 48=4*11+4*3=56, which is false.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula A181278Formula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var first = Call("fst", p);
        var second = Call("snd", p);
        var parityFirst = Parity(n, first);
        var paritySecond = Parity(n, second);
        var dot = DotParity(n, first, second);
        var rowOrder = Less(first, second);
        var gramOrder = Greater(
            Add(Multiply(D(2), Parenthesized(parityFirst)), Parenthesized(dot)),
            Add(Multiply(D(2), Parenthesized(dot)), Parenthesized(paritySecond)));
        var predicate = Lambda(p, Call("decide", And(rowOrder, gramOrder)));
        var rows = Call("range", new Formula.Power(D(2), n));
        var pairs = Call("product", rows, rows);
        return Disp(Universal("n", Equal(
            Call("a181278", n), Call("countP", predicate, pairs))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var premise = LessOrEqual(D(4), n);
        var left = Add(Call("a181278", n),
            Multiply(D(1, 6), Call("a181278", Subtract(n, D(3)))));
        var right = Add(
            Multiply(D(4), Call("a181278", Subtract(n, D(1)))),
            Multiply(D(4), Call("a181278", Subtract(n, D(2)))));
        var quantified = Universal("n", Implies(premise, Equal(left, right)));
        return Disp(Iff(Parenthesized(F.Id("claim")), Parenthesized(quantified)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Parity(Formula n, Formula row)
    {
        var i = F.Id("i");
        var selected = Call("filter", Lambda(i, Call("testBit", row, i)),
            Call("range", n));
        return new Formula.Modulo(Call("length", selected), D(2));
    }

    private static Formula DotParity(Formula n, Formula left, Formula right)
    {
        var i = F.Id("i");
        var bothBits = Parenthesized(And(
            Call("testBit", left, i), Call("testBit", right, i)));
        var selected = Call("filter", Lambda(i, bothBits), Call("range", n));
        return new Formula.Modulo(Call("length", selected), D(2));
    }

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(variable, Sp, Mapsto, Sp, body));
    private static Formula Universal(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            Naturals(), body);
    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
