using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class MurthyLeastPrimePrefixSuffixRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/murthy2002a018800");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The value a(1) = 11 refutes Murthy's suffix bound for OEIS A018800.",
        H("The OEIS A018800 Prime-Prefix Suffix-Bound Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("a018800-sequence"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The A018800 sequence"),
                StatementSource.FromAuthor(SequenceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The interval condition expresses the decimal-prefix reading of "
                        + "begins with n. The natural infimum is zero when the set is empty."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a018800-suffix-bound-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Murthy's suffix-bound conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The positive suffix length makes the appended suffix nonempty. Its "
                        + "value is below 10 to that length, and the conjecture requires it "
                        + "to be strictly smaller than the prefix."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a018800-suffix-bound-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture fails at n = 1"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At n = 1, the least prime with decimal prefix 1 is a(1) = 11. Taking "
                        + "a suffix of length one and value one gives 11 = 1 times 10 plus 1, "
                        + "while one is not strictly smaller than one. No general existence "
                        + "statement for a(n) is asserted."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a018800-least-prime-prefix-suffix-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var m = F.Id("m");
        var power = Power(D(1, 0), m);
        var interval = And(
            LessOrEqual(Multiply(n, power), p),
            Less(p, Multiply(Add(n, D(1)), power)));
        var suffixLength = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("m"),
            Naturals(),
            interval);
        var conditions = And(Call("Prime", p), suffixLength);
        var prefixPrimes = Seq(
            OpenBrace, p, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            conditions, CloseBrace);
        return Disp(All("n", Equal(Call("a", n), Call("sInf", prefixPrimes))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var k = F.Id("k");
        var power = Power(D(1, 0), m);
        var conclusion = Implies(
            LessOrEqual(D(1), n),
            Implies(
                LessOrEqual(D(1), m),
                Implies(
                    Less(k, power),
                    Implies(
                        Equal(Call("a", n), Add(Multiply(n, power), k)),
                        Less(k, n)))));
        var quantified = All("n", All("m", All("k", conclusion)));
        return Disp(Iff(
            Parenthesized(F.Id("claim")),
            Parenthesized(quantified)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

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

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

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

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
