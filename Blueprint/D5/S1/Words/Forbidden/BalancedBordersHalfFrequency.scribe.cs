using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Forbidden;

internal sealed class BalancedBordersHalfFrequencyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/bonamagarichey2026letter");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced borders force exact half frequency; short unbalanced words exclude it.", H("BalancedBordersHalfFrequency"),
        Blocks(
            Describe.Lean(DescribeId.Create("rho-nonneg"),
                DeclarationHandle.Create(Prefix + "rho_nonneg"), H("rho_nonneg"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), LeqF(Num(0), Call("rho", F.Id("w"), F.Id("m"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rho-le-one"),
                DeclarationHandle.Create(Prefix + "rho_le_one"), H("rho_le_one"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), Imp(NotEqual(F.Id("w"), Nil()), Imp(LtF(Num(0), F.Id("m")), LeqF(Call("rho", F.Id("w"), F.Id("m")), Num(1)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-not-tendsto-half"),
                DeclarationHandle.Create(Prefix + "singleton_not_tendsto_half"), H("singleton_not_tendsto_half"),
                StatementSource.FromAuthor(Disp(All("b", F.Id("Bool"), new Formula.Not(Call("Tendsto", Call("rho", ListLit(F.Id("b"))), F.Id("atTop"), Call("nhds", new Formula.Fraction(Num(1), Num(2)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flip-tendsto-half-iff"),
                DeclarationHandle.Create(Prefix + "flip_tendsto_half_iff"), H("flip_tendsto_half_iff"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), IffF(Call("Tendsto", Call("rho", Qualified("List", "map", Qualified("Bool", "not"), F.Id("w"))), F.Id("atTop"), Call("nhds", new Formula.Fraction(Num(1), Num(2)))), Call("Tendsto", Call("rho", F.Id("w")), F.Id("atTop"), Call("nhds", new Formula.Fraction(Num(1), Num(2))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complementing every bit bijects the avoiding words and replaces each positive-length average by one minus that average. Half-frequency convergence is preserved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("onestotal11-bound"),
                DeclarationHandle.Create(Prefix + "onesTotal11_bound"), H("onesTotal11_bound"),
                StatementSource.FromAuthor(Disp(All("k", N(), And(LeqF(Multiply(Num(3), Call("avoidOnes", ListLit(F.Id("true"), F.Id("true")), Add(F.Id("k"), Num(2)))), Multiply(Cast(Add(F.Id("k"), Num(2)), R()), Call("avoidCount", ListLit(F.Id("true"), F.Id("true")), Add(F.Id("k"), Num(2))))), LeqF(Multiply(Num(3), Call("avoidOnes", ListLit(F.Id("true"), F.Id("true")), Add(F.Id("k"), Num(3)))), Multiply(Cast(Add(F.Id("k"), Num(3)), R()), Call("avoidCount", ListLit(F.Id("true"), F.Id("true")), Add(F.Id("k"), Num(3))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The avoiding words for 11 split into a word prefixed by 0 and a shorter word prefixed by 10. Their disjoint count and one-count recurrences give the two inequalities simultaneously by induction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("not-tendsto-half-11"),
                DeclarationHandle.Create(Prefix + "not_tendsto_half_11"), H("not_tendsto_half_11"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Call("Tendsto", Call("rho", ListLit(F.Id("true"), F.Id("true"))), F.Id("atTop"), Call("nhds", new Formula.Fraction(Num(1), Num(2))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The recurrence estimate bounds all positive-length averages from length two onward by 1/3, excluding convergence to 1/2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedmoment"),
                DeclarationHandle.Create(Prefix + "signedMoment"), H("signedMoment"),
                StatementSource.FromAuthor(Disp(All("f", Call("PowerSeries", Call("Polynomial", Q())), Equal(Call("signedMoment", F.Id("f")), Qualified("PowerSeries", "mk", LambdaF("n", N(), Subtract(Multiply(Num(2), Qualified("Polynomial", "eval", Num(1), Qualified("Polynomial", "derivative", Qualified("PowerSeries", "coeff", F.Id("n"), F.Id("f"))))), Multiply(Cast(F.Id("n"), Q()), Qualified("Polynomial", "eval", Num(1), Qualified("PowerSeries", "coeff", F.Id("n"), F.Id("f"))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signedmoment-add"),
                DeclarationHandle.Create(Prefix + "signedMoment_add"), H("signedMoment_add"),
                StatementSource.FromAuthor(Disp(All("f", Call("PowerSeries", Call("Polynomial", Q())), All("g", Call("PowerSeries", Call("Polynomial", Q())), Equal(Call("signedMoment", Add(F.Id("f"), F.Id("g"))), Add(Call("signedMoment", F.Id("f")), Call("signedMoment", F.Id("g")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedmoment-sub"),
                DeclarationHandle.Create(Prefix + "signedMoment_sub"), H("signedMoment_sub"),
                StatementSource.FromAuthor(Disp(All("f", Call("PowerSeries", Call("Polynomial", Q())), All("g", Call("PowerSeries", Call("Polynomial", Q())), Equal(Call("signedMoment", Subtract(F.Id("f"), F.Id("g"))), Subtract(Call("signedMoment", F.Id("f")), Call("signedMoment", F.Id("g")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedmoment-mul"),
                DeclarationHandle.Create(Prefix + "signedMoment_mul"), H("signedMoment_mul"),
                StatementSource.FromAuthor(Disp(All("f", Call("PowerSeries", Call("Polynomial", Q())), All("g", Call("PowerSeries", Call("Polynomial", Q())), Equal(Call("signedMoment", Multiply(F.Id("f"), F.Id("g"))), Add(Multiply(Call("signedMoment", F.Id("f")), Qualified("PowerSeries", "map", Qualified("Polynomial", "evalRingHom", Num(1)), F.Id("g"))), Multiply(Qualified("PowerSeries", "map", Qualified("Polynomial", "evalRingHom", Num(1)), F.Id("f")), Call("signedMoment", F.Id("g"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedmoment-one"),
                DeclarationHandle.Create(Prefix + "signedMoment_one"), H("signedMoment_one"),
                StatementSource.FromAuthor(Disp(Equal(Call("signedMoment", Num(1)), Num(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedmoment-monomial"),
                DeclarationHandle.Create(Prefix + "signedMoment_monomial"), H("signedMoment_monomial"),
                StatementSource.FromAuthor(Disp(All("n", N(), All("k", N(), Equal(Call("signedMoment", Qualified("PowerSeries", "monomial", F.Id("n"), Pow(Qualified("Polynomial", "X"), F.Id("k")))), Qualified("PowerSeries", "monomial", F.Id("n"), Subtract(Multiply(Num(2), Cast(F.Id("k"), Q())), Cast(F.Id("n"), Q())))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedmoment-letterseries"),
                DeclarationHandle.Create(Prefix + "signedMoment_letterSeries"), H("signedMoment_letterSeries"),
                StatementSource.FromAuthor(Disp(Equal(Call("signedMoment", Call("letterSeries")), Num(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedmoment-sum"),
                DeclarationHandle.Create(Prefix + "signedMoment_sum"), H("signedMoment_sum"),
                StatementSource.FromAuthor(Disp(All("I", F.Id("Type"), All("S", Call("Finset", F.Id("I")), All("f", new Formula.TypeArrow(F.Id("I"), Call("PowerSeries", Call("Polynomial", Q()))), Equal(Call("signedMoment", SumOver("i", F.Id("S"), Call("f", F.Id("i")))), SumOver("i", F.Id("S"), Call("signedMoment", Call("f", F.Id("i")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("avoiddenominator"),
                DeclarationHandle.Create(Prefix + "avoidDenominator"), H("avoidDenominator"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Equal(Call("avoidDenominator", F.Id("w")), Add(Multiply(Subtract(Num(1), Call("letterSeries")), Call("overlapSeries", F.Id("w"))), Call("wordMonomial", F.Id("w"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("balanced-signedmoment-avoidseries"),
                DeclarationHandle.Create(Prefix + "balanced_signedMoment_avoidSeries"), H("balanced_signedMoment_avoidSeries"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), Imp(Call("BalancedBorders", F.Id("w")), Equal(Call("signedMoment", Call("avoidSeries", F.Id("w"))), Num(0))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-tendsto-half"),
                DeclarationHandle.Create(Prefix + "balanced_tendsto_half"), H("balanced_tendsto_half"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), Imp(Call("BalancedBorders", F.Id("w")), Call("Tendsto", Call("rho", F.Id("w")), F.Id("atTop"), Call("nhds", new Formula.Fraction(Num(1), Num(2))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("balanced_tendsto_half"), Paragraph(Text("Only the rho consequence is displayed. The proof gives rho w m = 1/2 for every positive m."))), DescribeRole.Theorem))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));

    private static Formula Word() => Call("List", F.Id("Bool"));
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);
    private static Formula ListLit(params Formula[] xs) => Seq(OpenBracket, Arguments(xs), CloseBracket);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Arguments(Formula[] xs) => Seq(xs.SelectMany((x, i) =>
        i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray());
    private static Formula Qualified(string owner, string name, params Formula[] xs) =>
        xs.Length == 0 ? Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name))) :
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)), Parenthesized(Arguments(xs)));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);


    private static Formula LambdaF(string name, Formula type, Formula body) =>
        Seq(Parenthesized(Seq(F.Id(name), Colon, type)), Mapsto, Parenthesized(body));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, type));
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LeqF(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtF(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula SumOver(string name, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, domain), Sp, Parenthesized(body));

    private static Formula SourceRho() => Seq(Rho, Underscore, Grp(F.Id("n")), Caret, Grp(F.Id("w")));
    private static Formula SourceRhoLimit() => new Formula.Power(Rho, F.Id("w"));
    private static Formula SourceBorders() => Seq(Mathcal, Grp(F.Id("B")), Parenthesized(Seq(F.Id("w"), Comma, F.Id("w"))));
    private static Formula SourceLength(Formula a) => Seq(Bar, a, Bar);
    private static Formula SourceOnes(Formula a) => new Formula.Subscript(SourceLength(a), Num(1));
    private static DocumentBlock Quote(string name) => name switch
    {
        "omega" => Paragraph(Text("“For positive integer "), Math(Seq(F.Id("n"), Geq, Num(1))),
            Text(" and any word "), Math(F.Id("w")), Text(" of length "), Math(F.Id("k")),
            Text(", denote by "), Text("Ωₙʷ"), Text(" the set of words of length "), Math(F.Id("n")),
            Text(" with no "), Math(F.Id("w")), Text(" factor, i.e.” (Definition 2.1, p. 3.)")),
        "rho" => Paragraph(Text("“For any word "), Math(F.Id("w")), Text(" and positive integer "),
            Math(F.Id("n")), Text(", denote by "), Math(SourceRho()),
            Text(" the frequency of "), Math(Num(1)), Text("s over all words in "), Text("Ωₙʷ"),
            Text(":” (Definition 2.4, pp. 3–4.) “Set "),
            Math(Seq(SourceRhoLimit(), Eq, Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                SourceRho(), Sp, InMacro, Sp, OpenBracket, Num(0), Comma, Num(1), CloseBracket)),
            Text(" if it exists.” (p. 4.)")),
        "IsBorder" => Paragraph(Text("“Fix two words "), Math(F.Id("v")), Text(", "), Math(F.Id("w")),
            Text(" with "), Math(Seq(F.Id("v"), Sp, InMacro, Sp,
                new Formula.Power(new Formula.SetLiteral([Num(0), Num(1)]), F.Id("k")))),
            Text(". Denote by "), Math(Seq(Mathcal, Grp(F.Id("B")), Parenthesized(Seq(F.Id("v"), Comma, F.Id("w"))))),
            Text(" the set of borders of "), Math(F.Id("v")), Text(" and "), Math(F.Id("w")),
            Text(":” (Definition 2.6, p. 4.)")),
        "BalancedBorders" => Paragraph(Text("“A word "), Math(F.Id("w")),
            Text(" has balanced borders if for all "), Math(Member(F.Id("b"), SourceBorders())), Text(", "),
            Math(Equal(SourceLength(F.Id("b")), Seq(Num(2), SourceOnes(F.Id("b"))))),
            Text(".” (Definition 3.2, p. 9.)")),
        "balanced_tendsto_half" => Paragraph(Text("“In particular, if "), Math(F.Id("w")),
            Text(" has balanced borders, then "), Math(Seq(SourceRhoLimit(), Eq,
                new Formula.Power(F.Id("q"), F.Id("w")), Eq, new Formula.Fraction(Num(1), Num(2)))),
            Text(".” (Proposition 3.3, p. 9.)")),
        "claim" => Paragraph(Text("“A word "), Math(F.Id("w")), Text(" has "),
            Math(Equal(SourceRhoLimit(), Seq(Num(1), Slash, Num(2)))),
            Text(" if and only if "), Math(F.Id("w")), Text(" has balanced borders. The same holds with "),
            Math(SourceRhoLimit()), Text(" replaced by "), Math(new Formula.Power(F.Id("q"), F.Id("w"))),
            Text(".” (Conjecture 6.1, p. 20.)")),
        _ => throw new ArgumentException("No quoted source definition."),
    };
}
