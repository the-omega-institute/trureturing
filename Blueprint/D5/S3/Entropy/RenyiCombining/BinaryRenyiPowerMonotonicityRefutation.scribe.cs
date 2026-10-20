using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class BinaryRenyiPowerMonotonicityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/liu2026binaryentropybounds");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powered binary Renyi entropy can decrease as its positive order increases.",
        H("A decrease between orders one quarter and one half"),
        Blocks(
            Definition("powered", "The powered binary entropy", PoweredFormula(),
                Blocks(
                    Paragraph(Text("The binary Renyi entropy with natural logarithms is")),
                    new DocumentBlock.DisplayFormula(EntropyFormula()),
                    Paragraph(Text("The normalization is log(2), and the outer exponent is a real power. "
                        + "This is the expression in Liu's question in Section 1.4(b).")))),
            Definition("claim", "Monotonicity in the order", ClaimFormula(),
                Blocks(Paragraph(Text(
                    "For every binary probability, the proposed monotonicity compares any two "
                        + "positive orders a < b distinct from one. Order one is excluded because "
                        + "the source defines its entropy by a limit.")))),
            Result()
        )));

    private static DocumentBlock Definition(string declaration, string title, Formula formula,
        BlockSequence commentary) => Describe.Lean(
            DescribeId.Create("liu-binary-renyi-power-" + declaration),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            commentary, DescribeRole.Definition);

    private static DocumentBlock Result() => Describe.Lean(
        DescribeId.Create("liu-binary-renyi-power-result"),
        DeclarationHandle.Create(Prefix + "result"), H("The monotonicity proposition is false"),
        StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
        AssessedProvenance.FromRepo(Source),
        Blocks(
            Paragraph(Text("Take x = 1/17 and the orders 1/4 and 1/2. "
                + "The identities 16^(1/4) = 2 and 16^(1/2) = 4 give the closed forms")),
            new DocumentBlock.DisplayFormula(QuarterEntropyFormula()),
            new DocumentBlock.DisplayFormula(HalfEntropyFormula()),
            Paragraph(Text("The integer comparisons 17^4 times 2^9 < 3^16 and "
                + "25^16 < 17^16 times 2^9 imply, by strict monotonicity of the natural logarithm,")),
            new DocumentBlock.DisplayFormula(LogComparisonFormula()),
            Paragraph(Text("Since log(2) is positive, these comparisons give "
                + "hRenyi(1/4,1/17)/log(2) > 3/4 and "
                + "0 < hRenyi(1/2,1/17)/log(2) < 9/16. "
                + "Raising the positive bounds to the eighth and fourth powers, respectively, "
                + "and using (3/4)^8 = (9/16)^4 yields "
                + "powered(1/2,1/17) < powered(1/4,1/17). "
                + "Both orders are positive and distinct from one, and 1/17 lies in [0,1]."))),
        DescribeRole.Theorem,
        new OpenProblemResolutionClaim(
            ProblemSlugRef.Create("liu-2026-powered-binary-renyi-monotonicity-refutation"),
            ResolutionKind.Refuted));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), RealType(), body);
    private static Formula Rel(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Imp(Formula premise, Formula body) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(body));
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula LogOf(Formula value) => new Formula.Apply(Qualified("Real", "log"), [value]);

    private static Formula EntropyFormula()
    {
        Formula alpha = F.Id("alpha"), x = F.Id("x");
        return All("alpha", All("x", Rel(Call("hRenyi", alpha, x), FormulaRelationOperator.Equal,
            Multiply(Fraction(D(1), Subtract(D(1), alpha)),
                LogOf(Add(new Formula.Power(x, alpha),
                    new Formula.Power(Parenthesized(Subtract(D(1), x)), alpha)))))));
    }

    private static Formula PoweredFormula()
    {
        Formula alpha = F.Id("alpha"), x = F.Id("x");
        return All("alpha", All("x", Rel(Call("powered", alpha, x), FormulaRelationOperator.Equal,
            new Formula.Power(
                Parenthesized(Fraction(Call("hRenyi", alpha, x), LogOf(D(2)))),
                Fraction(D(2), alpha)))));
    }

    private static Formula ClaimFormula()
    {
        Formula x = F.Id("x"), a = F.Id("a"), b = F.Id("b");
        Formula comparison = Rel(Call("powered", a, x), FormulaRelationOperator.LessThanOrEqual,
            Call("powered", b, x));
        Formula orders = All("a", All("b",
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, a),
            Imp(Rel(a, FormulaRelationOperator.LessThan, b),
            Imp(new Formula.Not(Rel(a, FormulaRelationOperator.Equal, D(1))),
            Imp(new Formula.Not(Rel(b, FormulaRelationOperator.Equal, D(1))), comparison))))));
        Formula proposition = All("x",
            Imp(Rel(x, FormulaRelationOperator.MemberOf,
                Seq(OpenBracket, D(0), Comma, Sp, D(1), CloseBracket)), orders));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(proposition));
    }

    private static Formula QuarterEntropyFormula() => Rel(
        Call("hRenyi", Fraction(D(1), D(4)), Fraction(D(1), D(1, 7))),
        FormulaRelationOperator.Equal,
        Multiply(Fraction(D(4), D(3)),
            Parenthesized(Subtract(LogOf(D(3)), Fraction(LogOf(D(1, 7)), D(4))))));

    private static Formula HalfEntropyFormula() => Rel(
        Call("hRenyi", Fraction(D(1), D(2)), Fraction(D(1), D(1, 7))),
        FormulaRelationOperator.Equal, LogOf(Fraction(D(2, 5), D(1, 7))));

    private static Formula LogComparisonFormula() => new Formula.Logic(
        Rel(Add(Multiply(D(4), LogOf(D(1, 7))), Multiply(D(9), LogOf(D(2)))),
            FormulaRelationOperator.LessThan, Multiply(D(1, 6), LogOf(D(3)))),
        FormulaLogicOperator.And,
        Rel(Multiply(D(1, 6), LogOf(Fraction(D(2, 5), D(1, 7)))),
            FormulaRelationOperator.LessThan, Multiply(D(9), LogOf(D(2)))));
}
