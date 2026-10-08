using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Forbidden;

internal sealed class ForbiddenWordGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Forbidden/ForbiddenWordGrowth.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/bonamagarichey2026letter");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoidance growth and escaping weighted averages control the boundary limit.", H("ForbiddenWordGrowth"),
        Blocks(
            Describe.Lean(DescribeId.Create("avoidcount"),
                DeclarationHandle.Create(Prefix + "avoidCount"), H("avoidCount"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), Equal(Call("avoidCount", F.Id("w"), F.Id("m")), Cast(Qualified("Finset", "card", Call("omega", F.Id("w"), F.Id("m"))), R())))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("avoidcount-pos"),
                DeclarationHandle.Create(Prefix + "avoidCount_pos"), H("avoidCount_pos"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), Imp(NotEqual(F.Id("w"), Nil()), LtF(Num(0), Call("avoidCount", F.Id("w"), F.Id("m")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("avoidcount-submultiplicative"),
                DeclarationHandle.Create(Prefix + "avoidCount_submultiplicative"), H("avoidCount_submultiplicative"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), All("n", N(), LeqF(Call("avoidCount", F.Id("w"), Add(F.Id("m"), F.Id("n"))), Multiply(Call("avoidCount", F.Id("w"), F.Id("m")), Call("avoidCount", F.Id("w"), F.Id("n"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("log-avoidcount-subadditive"),
                DeclarationHandle.Create(Prefix + "log_avoidCount_subadditive"), H("log_avoidCount_subadditive"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), Call("Subadditive", LambdaF("m", N(), Qualified("Real", "log", Call("avoidCount", F.Id("w"), F.Id("m"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growthrate"),
                DeclarationHandle.Create(Prefix + "growthRate"), H("growthRate"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), Equal(Call("growthRate", F.Id("w"), F.Id("hw")), Qualified("Real", "exp", Call("sInf", Qualified("Set", "image", LambdaF("n", N(), new Formula.Fraction(Qualified("Real", "log", Call("avoidCount", F.Id("w"), F.Id("n"))), Cast(F.Id("n"), R()))), Qualified("Set", "Ici", Num(1)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exponential of the logarithmic Fekete limit is the avoidance growth rate. The proof argument hw certifies nonemptiness."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("growthrate-lower-power"),
                DeclarationHandle.Create(Prefix + "growthRate_lower_power"), H("growthRate_lower_power"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("m", N(), LeqF(Pow(Call("growthRate", F.Id("w"), F.Id("hw")), F.Id("m")), Call("avoidCount", F.Id("w"), F.Id("m")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growthrate-lt-two"),
                DeclarationHandle.Create(Prefix + "growthRate_lt_two"), H("growthRate_lt_two"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), LtF(Call("growthRate", F.Id("w"), F.Id("hw")), Num(2)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-avoidcount-summable"),
                DeclarationHandle.Create(Prefix + "weighted_avoidCount_summable"), H("weighted_avoidCount_summable"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("q", N(), All("x", R(), Imp(LeqF(Num(0), F.Id("x")), Imp(LtF(Multiply(Call("growthRate", F.Id("w"), F.Id("hw")), F.Id("x")), Num(1)), Call("Summable", LambdaF("m", N(), Multiply(Multiply(Pow(Cast(F.Id("m"), R()), F.Id("q")), Call("avoidCount", F.Id("w"), F.Id("m"))), Pow(F.Id("x"), F.Id("m"))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inside the reciprocal growth radius, the counts are eventually bounded by a larger exponential rate whose product with x is less than one. Polynomial length weights remain summable."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("avoidcount-summable"),
                DeclarationHandle.Create(Prefix + "avoidCount_summable"), H("avoidCount_summable"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("x", R(), Imp(LeqF(Num(0), F.Id("x")), Imp(LtF(Multiply(Call("growthRate", F.Id("w"), F.Id("hw")), F.Id("x")), Num(1)), Call("Summable", LambdaF("m", N(), Multiply(Call("avoidCount", F.Id("w"), F.Id("m")), Pow(F.Id("x"), F.Id("m")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-tsum-tendsto"),
                DeclarationHandle.Create(Prefix + "weighted_tsum_tendsto"), H("weighted_tsum_tendsto"),
                StatementSource.FromAuthor(Disp(All("T", F.Id("Type"), All("F", Call("Filter", F.Id("T")), All("p", new Formula.TypeArrow(F.Id("T"), new Formula.TypeArrow(N(), R())), All("u", new Formula.TypeArrow(N(), R()), All("L", R(), All("B", R(), Imp(All("t", F.Id("T"), All("n", N(), LeqF(Num(0), Call("p", F.Id("t"), F.Id("n"))))), Imp(All("t", F.Id("T"), Call("Summable", Call("p", F.Id("t")))), Imp(All("t", F.Id("T"), Equal(Tsum("n", N(), Call("p", F.Id("t"), F.Id("n"))), Num(1))), Imp(LeqF(Num(0), F.Id("B")), Imp(All("n", N(), LeqF(new Formula.Absolute(Subtract(Call("u", F.Id("n")), F.Id("L"))), F.Id("B"))), Imp(Call("Tendsto", F.Id("u"), F.Id("atTop"), Call("nhds", F.Id("L"))), Imp(All("N", N(), Call("Tendsto", LambdaF("t", F.Id("T"), SumOver("n", Qualified("Finset", "range", F.Id("N")), Call("p", F.Id("t"), F.Id("n")))), F.Id("F"), Call("nhds", Num(0)))), Call("Tendsto", LambdaF("t", F.Id("T"), Tsum("n", N(), Multiply(Call("p", F.Id("t"), F.Id("n")), Call("u", F.Id("n"))))), F.Id("F"), Call("nhds", F.Id("L")))))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weights are nonnegative, summable and have total one. Their mass on every finite initial segment tends to zero along F. A uniformly bounded error and convergence of u give convergence of the weighted averages to L. No nontriviality assumption on F is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("avoidones-bounds"),
                DeclarationHandle.Create(Prefix + "avoidOnes_bounds"), H("avoidOnes_bounds"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), And(LeqF(Num(0), Call("avoidOnes", F.Id("w"), F.Id("m"))), LeqF(Call("avoidOnes", F.Id("w"), F.Id("m")), Multiply(Cast(F.Id("m"), R()), Call("avoidCount", F.Id("w"), F.Id("m"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The total number of ones is nonnegative and at most the length times the number of avoiding words."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("avoidones"),
                DeclarationHandle.Create(Prefix + "avoidOnes"), H("avoidOnes"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), Equal(Call("avoidOnes", F.Id("w"), F.Id("m")), SumOver("u", Call("omega", F.Id("w"), F.Id("m")), Cast(Qualified("List", "count", F.Id("true"), F.Id("u")), R()))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Word() => Call("List", F.Id("Bool"));
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Arguments(Formula[] xs) => Seq(xs.SelectMany((x, i) =>
        i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray());
    private static Formula Qualified(string owner, string name, params Formula[] xs) =>
        xs.Length == 0 ? Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name))) :
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)), Parenthesized(Arguments(xs)));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula AllProp(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Parenthesized(type))), Comma, Sp, body);

    private static Formula LambdaF(string name, Formula type, Formula body) =>
        Seq(Parenthesized(Seq(F.Id(name), Colon, type)), Mapsto, Parenthesized(body));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));

    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, type));

    private static Formula LeqF(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtF(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula SumOver(string name, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, domain), Sp, Parenthesized(body));
    private static Formula Tsum(string name, Formula type, Formula body) =>
        Seq(Sum, Apos, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body));

}
