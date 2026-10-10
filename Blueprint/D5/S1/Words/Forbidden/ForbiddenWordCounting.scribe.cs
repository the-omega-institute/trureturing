using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Forbidden;

internal sealed class ForbiddenWordCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Forbidden/ForbiddenWordCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/bonamagarichey2026letter");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-hit decompositions give the forbidden binary-word counting identity.", H("ForbiddenWordCounting"),
        Blocks(
            Describe.Lean(DescribeId.Create("words"),
                DeclarationHandle.Create(Prefix + "words"), H("words"),
                StatementSource.FromAuthor(Disp(All("m", N(), Equal(Call("words", F.Id("m")), Qualified("Finset", "image", Qualified("List", "ofFn"), Cast(Qualified("Finset", "univ"), Call("Finset", new Formula.TypeArrow(Call("Fin", F.Id("m")), F.Id("Bool"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The image of all functions from Fin m to Bool under List.ofFn is precisely the set of length-m binary lists, including the empty list when m is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mem-words"),
                DeclarationHandle.Create(Prefix + "mem_words"), H("mem_words"),
                StatementSource.FromAuthor(Disp(All("m", N(), All("u", Word(), IffF(Member(F.Id("u"), Call("words", F.Id("m"))), Equal(Qualified("List", "length", F.Id("u")), F.Id("m"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("omega"),
                DeclarationHandle.Create(Prefix + "omega"), H("omega"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), Equal(Call("omega", F.Id("w"), F.Id("m")), Qualified("Finset", "filter", LambdaF("u", Word(), new Formula.Not(Qualified("List", "IsInfix", F.Id("w"), F.Id("u")))), Call("words", F.Id("m")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("omega"), Paragraph(Text("Words are List Bool, true is 1, and List.IsInfix is factor containment. The source definition at positive lengths is extended to length zero by the same filter."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mem-omega"),
                DeclarationHandle.Create(Prefix + "mem_omega"), H("mem_omega"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("u", Word(), All("m", N(), IffF(Member(F.Id("u"), Call("omega", F.Id("w"), F.Id("m"))), And(Equal(Qualified("List", "length", F.Id("u")), F.Id("m")), new Formula.Not(Qualified("List", "IsInfix", F.Id("w"), F.Id("u")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rho"),
                DeclarationHandle.Create(Prefix + "rho"), H("rho"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), Equal(Call("rho", F.Id("w"), F.Id("m")), new Formula.Fraction(SumOver("u", Call("omega", F.Id("w"), F.Id("m")), Cast(Qualified("List", "count", F.Id("true"), F.Id("u")), R())), Multiply(Cast(F.Id("m"), R()), Cast(Qualified("Finset", "card", Call("omega", F.Id("w"), F.Id("m"))), R())))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("rho"), Paragraph(Text("The quotient is the literal source sum divided by m times the number of avoiding words. List.count true counts ones. Counts are coerced into the reals; division is real division. The value at m = 0 is a totalization that has no effect on convergence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("isborder"),
                DeclarationHandle.Create(Prefix + "IsBorder"), H("IsBorder"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("b", Word(), IffF(Call("IsBorder", F.Id("w"), F.Id("b")), And(NotEqual(F.Id("b"), Nil()), And(Qualified("List", "IsPrefix", F.Id("b"), F.Id("w")), Qualified("List", "IsSuffix", F.Id("b"), F.Id("w"))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("IsBorder"), Paragraph(Text("The source border relation is specialized to v = w. Nonempty words are both a prefix and a suffix; the whole word is included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("balancedborders"),
                DeclarationHandle.Create(Prefix + "BalancedBorders"), H("BalancedBorders"),
                StatementSource.FromAuthor(Disp(All("w", Word(), IffF(Call("BalancedBorders", F.Id("w")), All("b", Word(), Imp(Call("IsBorder", F.Id("w"), F.Id("b")), Equal(Multiply(Num(2), Qualified("List", "count", F.Id("true"), F.Id("b"))), Qualified("List", "length", F.Id("b"))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("BalancedBorders"), Paragraph(Text("The displayed equality has the two sides exchanged and uses List.count true for the number of ones."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("self-border"),
                DeclarationHandle.Create(Prefix + "self_border"), H("self_border"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), Call("IsBorder", F.Id("w"), F.Id("w")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("avoidcoeff"),
                DeclarationHandle.Create(Prefix + "avoidCoeff"), H("avoidCoeff"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), Equal(Call("avoidCoeff", F.Id("w"), F.Id("m")), SumOver("u", Call("omega", F.Id("w"), F.Id("m")), Pow(Qualified("Polynomial", "X"), Qualified("List", "count", F.Id("true"), F.Id("u"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("avoidseries"),
                DeclarationHandle.Create(Prefix + "avoidSeries"), H("avoidSeries"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Equal(Call("avoidSeries", F.Id("w")), Qualified("PowerSeries", "mk", Call("avoidCoeff", F.Id("w"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wordmonomial"),
                DeclarationHandle.Create(Prefix + "wordMonomial"), H("wordMonomial"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Equal(Call("wordMonomial", F.Id("w")), Qualified("PowerSeries", "monomial", Qualified("List", "length", F.Id("w")), Pow(Qualified("Polynomial", "X"), Qualified("List", "count", F.Id("true"), F.Id("w")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("avoidcoeff-zero"),
                DeclarationHandle.Create(Prefix + "avoidCoeff_zero"), H("avoidCoeff_zero"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), Equal(Call("avoidCoeff", F.Id("w"), Num(0)), Num(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The empty word is the unique length-zero word avoiding a nonempty forbidden word, and its weight is one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("letterseries"),
                DeclarationHandle.Create(Prefix + "letterSeries"), H("letterSeries"),
                StatementSource.FromAuthor(Disp(Equal(Call("letterSeries"), Multiply(Qualified("PowerSeries", "X"), Qualified("PowerSeries", "C", Add(Num(1), Qualified("Polynomial", "X"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("borderlengths"),
                DeclarationHandle.Create(Prefix + "borderLengths"), H("borderLengths"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Equal(Call("borderLengths", F.Id("w")), Qualified("Finset", "filter", LambdaF("j", N(), And(LtF(Num(0), F.Id("j")), Qualified("List", "IsSuffix", Qualified("List", "take", F.Id("j"), F.Id("w")), F.Id("w")))), Qualified("Finset", "range", Add(Qualified("List", "length", F.Id("w")), Num(1)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("overlapseries"),
                DeclarationHandle.Create(Prefix + "overlapSeries"), H("overlapSeries"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Equal(Call("overlapSeries", F.Id("w")), SumOver("j", Call("borderLengths", F.Id("w")), Qualified("PowerSeries", "monomial", Qualified("Nat", "sub", Qualified("List", "length", F.Id("w")), F.Id("j")), Pow(Qualified("Polynomial", "X"), Qualified("List", "count", F.Id("true"), Qualified("List", "drop", F.Id("j"), F.Id("w")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("countingidentity"),
                DeclarationHandle.Create(Prefix + "countingIdentity"), H("countingIdentity"),
                StatementSource.FromAuthor(Disp(All("w", Word(), IffF(Call("countingIdentity", F.Id("w")), Equal(Multiply(Call("avoidSeries", F.Id("w")), Add(Multiply(Subtract(Num(1), Call("letterSeries")), Call("overlapSeries", F.Id("w"))), Call("wordMonomial", F.Id("w")))), Call("overlapSeries", F.Id("w"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("imbalance"),
                DeclarationHandle.Create(Prefix + "imbalance"), H("imbalance"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("j", N(), Equal(Call("imbalance", F.Id("w"), F.Id("j")), Subtract(Multiply(Num(2), Cast(Qualified("List", "count", F.Id("true"), Qualified("List", "take", F.Id("j"), F.Id("w"))), Z())), Cast(Qualified("List", "length", Qualified("List", "take", F.Id("j"), F.Id("w"))), Z()))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mem-borderlengths"),
                DeclarationHandle.Create(Prefix + "mem_borderLengths"), H("mem_borderLengths"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("j", N(), IffF(Member(F.Id("j"), Call("borderLengths", F.Id("w"))), And(LtF(Num(0), F.Id("j")), And(LeqF(F.Id("j"), Qualified("List", "length", F.Id("w"))), Qualified("List", "IsSuffix", Qualified("List", "take", F.Id("j"), F.Id("w")), F.Id("w"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("forbidden-word-counting-identity"),
                DeclarationHandle.Create(Prefix + "forbidden_word_counting_identity"), H("forbidden_word_counting_identity"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), Equal(Multiply(Call("avoidSeries", F.Id("w")), Add(Multiply(Subtract(Num(1), Call("letterSeries")), Call("overlapSeries", F.Id("w"))), Call("wordMonomial", F.Id("w")))), Call("overlapSeries", F.Id("w"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("This is the cleared-denominator form of the generating function identity in Fact 2.9, p. 5. A word is either avoiding or has a unique first-hit prefix. Appending the forbidden word records an overlap with a border. The two decompositions give the identity coefficient by coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-mem-borderlengths"),
                DeclarationHandle.Create(Prefix + "full_mem_borderLengths"), H("full_mem_borderLengths"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), Member(Qualified("List", "length", F.Id("w")), Call("borderLengths", F.Id("w"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("borderlengths-iff-border"),
                DeclarationHandle.Create(Prefix + "borderLengths_iff_border"), H("borderLengths_iff_border"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("b", Word(), IffF(Call("IsBorder", F.Id("w"), F.Id("b")), ExistsF("j", N(), And(Member(F.Id("j"), Call("borderLengths", F.Id("w"))), Equal(F.Id("b"), Qualified("List", "take", F.Id("j"), F.Id("w")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("omega-nonempty"),
                DeclarationHandle.Create(Prefix + "omega_nonempty"), H("omega_nonempty"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("m", N(), Imp(NotEqual(F.Id("w"), Nil()), Qualified("Finset", "Nonempty", Call("omega", F.Id("w"), F.Id("m")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Z() => new Formula.Integers();
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

    private static Formula ExistsF(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
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
