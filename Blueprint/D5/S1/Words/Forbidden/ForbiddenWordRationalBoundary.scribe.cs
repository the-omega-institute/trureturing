using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Forbidden;

internal sealed class ForbiddenWordRationalBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/bonamagarichey2026letter");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The avoidance denominator vanishes at the reciprocal growth rate.", H("ForbiddenWordRationalBoundary"),
        Blocks(
            Describe.Lean(DescribeId.Create("serieseval"),
                DeclarationHandle.Create(Prefix + "seriesEval"), H("seriesEval"),
                StatementSource.FromAuthor(Disp(All("f", Call("PowerSeries", R()), All("x", R(), Equal(Call("seriesEval", F.Id("f"), F.Id("x")), Tsum("m", N(), Multiply(Qualified("PowerSeries", "coeff", F.Id("m"), F.Id("f")), Pow(F.Id("x"), F.Id("m"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("realcountseries"),
                DeclarationHandle.Create(Prefix + "realCountSeries"), H("realCountSeries"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Equal(Call("realCountSeries", F.Id("w")), Qualified("PowerSeries", "mk", Call("avoidCount", F.Id("w"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("realimbalanceseries"),
                DeclarationHandle.Create(Prefix + "realImbalanceSeries"), H("realImbalanceSeries"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Equal(Call("realImbalanceSeries", F.Id("w")), Qualified("PowerSeries", "mk", LambdaF("m", N(), Subtract(Multiply(Num(2), Call("avoidOnes", F.Id("w"), F.Id("m"))), Multiply(Cast(F.Id("m"), R()), Call("avoidCount", F.Id("w"), F.Id("m")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("overlapeval"),
                DeclarationHandle.Create(Prefix + "overlapEval"), H("overlapEval"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("overlapEval", F.Id("w"), F.Id("x")), SumOver("j", Call("borderLengths", F.Id("w")), Pow(F.Id("x"), Qualified("Nat", "sub", Qualified("List", "length", F.Id("w")), F.Id("j"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("denomeval"),
                DeclarationHandle.Create(Prefix + "denomEval"), H("denomEval"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("denomEval", F.Id("w"), F.Id("x")), Add(Multiply(Subtract(Num(1), Multiply(Num(2), F.Id("x"))), Call("overlapEval", F.Id("w"), F.Id("x"))), Pow(F.Id("x"), Qualified("List", "length", F.Id("w"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("overlapmomenteval"),
                DeclarationHandle.Create(Prefix + "overlapMomentEval"), H("overlapMomentEval"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("overlapMomentEval", F.Id("w"), F.Id("x")), SumOver("j", Call("borderLengths", F.Id("w")), Multiply(Subtract(Multiply(Num(2), Cast(Qualified("List", "count", F.Id("true"), Qualified("List", "drop", F.Id("j"), F.Id("w"))), R())), Cast(Qualified("Nat", "sub", Qualified("List", "length", F.Id("w")), F.Id("j")), R())), Pow(F.Id("x"), Qualified("Nat", "sub", Qualified("List", "length", F.Id("w")), F.Id("j")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("denommomenteval"),
                DeclarationHandle.Create(Prefix + "denomMomentEval"), H("denomMomentEval"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("denomMomentEval", F.Id("w"), F.Id("x")), Add(Multiply(Subtract(Num(1), Multiply(Num(2), F.Id("x"))), Call("overlapMomentEval", F.Id("w"), F.Id("x"))), Multiply(Subtract(Multiply(Num(2), Cast(Qualified("List", "count", F.Id("true"), F.Id("w")), R())), Cast(Qualified("List", "length", F.Id("w")), R())), Pow(F.Id("x"), Qualified("List", "length", F.Id("w")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unbalanced-boundary-moment-ne-zero"),
                DeclarationHandle.Create(Prefix + "unbalanced_boundary_moment_ne_zero"), H("unbalanced_boundary_moment_ne_zero"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("z", R(), Imp(LeqF(Num(3), Qualified("List", "length", F.Id("w"))), Imp(new Formula.Not(Call("BalancedBorders", F.Id("w"))), Imp(LtF(new Formula.Fraction(Num(3), Num(2)), F.Id("z")), Imp(LtF(F.Id("z"), Num(2)), Imp(Equal(Multiply(Subtract(Num(2), F.Id("z")), Call("corrEval", F.Id("w"), F.Id("z"))), F.Id("z")), NotEqual(Call("denomMomentEval", F.Id("w"), new Formula.Fraction(Num(1), F.Id("z"))), Num(0))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a correlation root between 3/2 and 2, reciprocal evaluation converts the nonzero signed border polynomial into a nonzero denominator moment."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scalar-counting-identity"),
                DeclarationHandle.Create(Prefix + "scalar_counting_identity"), H("scalar_counting_identity"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("x", R(), Imp(LeqF(Num(0), F.Id("x")), Imp(LtF(Multiply(Call("growthRate", F.Id("w"), F.Id("hw")), F.Id("x")), Num(1)), Equal(Multiply(Call("seriesEval", Call("realCountSeries", F.Id("w")), F.Id("x")), Call("denomEval", F.Id("w"), F.Id("x"))), Call("overlapEval", F.Id("w"), F.Id("x")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluating the first-hit identity at a nonnegative point inside the growth radius gives the count-series identity. The summability hypotheses are derived from avoidance growth."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lengthmoment"),
                DeclarationHandle.Create(Prefix + "lengthMoment"), H("lengthMoment"),
                StatementSource.FromAuthor(Disp(All("f", Call("PowerSeries", R()), Equal(Call("lengthMoment", F.Id("f")), Multiply(Qualified("PowerSeries", "X"), Qualified("PowerSeries", "derivative", R(), F.Id("f"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coeff-lengthmoment"),
                DeclarationHandle.Create(Prefix + "coeff_lengthMoment"), H("coeff_lengthMoment"),
                StatementSource.FromAuthor(Disp(All("f", Call("PowerSeries", R()), All("m", N(), Equal(Qualified("PowerSeries", "coeff", F.Id("m"), Call("lengthMoment", F.Id("f"))), Multiply(Cast(F.Id("m"), R()), Qualified("PowerSeries", "coeff", F.Id("m"), F.Id("f")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reallengthseries"),
                DeclarationHandle.Create(Prefix + "realLengthSeries"), H("realLengthSeries"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Equal(Call("realLengthSeries", F.Id("w")), Call("lengthMoment", Call("realCountSeries", F.Id("w"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("overlaplengtheval"),
                DeclarationHandle.Create(Prefix + "overlapLengthEval"), H("overlapLengthEval"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("overlapLengthEval", F.Id("w"), F.Id("x")), SumOver("j", Call("borderLengths", F.Id("w")), Multiply(Cast(Qualified("Nat", "sub", Qualified("List", "length", F.Id("w")), F.Id("j")), R()), Pow(F.Id("x"), Qualified("Nat", "sub", Qualified("List", "length", F.Id("w")), F.Id("j")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("denomlengtheval"),
                DeclarationHandle.Create(Prefix + "denomLengthEval"), H("denomLengthEval"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("denomLengthEval", F.Id("w"), F.Id("x")), Add(Add(Multiply(Multiply(new Formula.Negate(Num(2)), F.Id("x")), Call("overlapEval", F.Id("w"), F.Id("x"))), Multiply(Subtract(Num(1), Multiply(Num(2), F.Id("x"))), Call("overlapLengthEval", F.Id("w"), F.Id("x")))), Multiply(Cast(Qualified("List", "length", F.Id("w")), R()), Pow(F.Id("x"), Qualified("List", "length", F.Id("w")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("scalar-length-identity"),
                DeclarationHandle.Create(Prefix + "scalar_length_identity"), H("scalar_length_identity"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("x", R(), Imp(LeqF(Num(0), F.Id("x")), Imp(LtF(Multiply(Call("growthRate", F.Id("w"), F.Id("hw")), F.Id("x")), Num(1)), Equal(Add(Multiply(Call("seriesEval", Call("realLengthSeries", F.Id("w")), F.Id("x")), Call("denomEval", F.Id("w"), F.Id("x"))), Multiply(Call("seriesEval", Call("realCountSeries", F.Id("w")), F.Id("x")), Call("denomLengthEval", F.Id("w"), F.Id("x")))), Call("overlapLengthEval", F.Id("w"), F.Id("x")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The length moment multiplies the coefficient of degree m by m. Its product rule turns the scalar count identity into the displayed length-weighted identity inside the growth radius."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scalar-moment-identity"),
                DeclarationHandle.Create(Prefix + "scalar_moment_identity"), H("scalar_moment_identity"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("x", R(), Imp(LeqF(Num(0), F.Id("x")), Imp(LtF(Multiply(Call("growthRate", F.Id("w"), F.Id("hw")), F.Id("x")), Num(1)), Equal(Add(Multiply(Call("seriesEval", Call("realImbalanceSeries", F.Id("w")), F.Id("x")), Call("denomEval", F.Id("w"), F.Id("x"))), Multiply(Call("seriesEval", Call("realCountSeries", F.Id("w")), F.Id("x")), Call("denomMomentEval", F.Id("w"), F.Id("x")))), Call("overlapMomentEval", F.Id("w"), F.Id("x")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed moment replaces each coefficient by twice the number of ones minus the total length. Its product rule gives the displayed signed identity inside the growth radius."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growthapproach"),
                DeclarationHandle.Create(Prefix + "growthApproach"), H("growthApproach"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("m", N(), Equal(Call("growthApproach", F.Id("w"), F.Id("hw"), F.Id("m")), new Formula.Fraction(Subtract(Num(1), new Formula.Fraction(Num(1), Add(Cast(F.Id("m"), R()), Num(2)))), Call("growthRate", F.Id("w"), F.Id("hw"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("growthapproach-pos"),
                DeclarationHandle.Create(Prefix + "growthApproach_pos"), H("growthApproach_pos"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("m", N(), LtF(Num(0), Call("growthApproach", F.Id("w"), F.Id("hw"), F.Id("m")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growthapproach-inside"),
                DeclarationHandle.Create(Prefix + "growthApproach_inside"), H("growthApproach_inside"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("m", N(), LtF(Multiply(Call("growthRate", F.Id("w"), F.Id("hw")), Call("growthApproach", F.Id("w"), F.Id("hw"), F.Id("m"))), Num(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growthapproach-tendsto"),
                DeclarationHandle.Create(Prefix + "growthApproach_tendsto"), H("growthApproach_tendsto"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), Call("Tendsto", Call("growthApproach", F.Id("w"), F.Id("hw")), F.Id("atTop"), Call("nhds", new Formula.Fraction(Num(1), Call("growthRate", F.Id("w"), F.Id("hw"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("overlapeval-ge-one"),
                DeclarationHandle.Create(Prefix + "overlapEval_ge_one"), H("overlapEval_ge_one"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Imp(NotEqual(F.Id("w"), Nil()), Imp(LeqF(Num(0), F.Id("x")), LeqF(Num(1), Call("overlapEval", F.Id("w"), F.Id("x"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countserieseval-growthapproach"),
                DeclarationHandle.Create(Prefix + "countSeriesEval_growthApproach"), H("countSeriesEval_growthApproach"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), All("m", N(), LeqF(Add(Cast(F.Id("m"), R()), Num(2)), Call("seriesEval", Call("realCountSeries", F.Id("w")), Call("growthApproach", F.Id("w"), F.Id("hw"), F.Id("m"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growthradius-denominator-zero"),
                DeclarationHandle.Create(Prefix + "growthRadius_denominator_zero"), H("growthRadius_denominator_zero"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), Equal(Call("denomEval", F.Id("w"), new Formula.Fraction(Num(1), Call("growthRate", F.Id("w"), F.Id("hw")))), Num(0)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The lower bound on the counts forces the scalar series to diverge along growthApproach. The counting identity bounds its denominator by a quantity tending to zero. Continuity gives vanishing at the reciprocal growth rate, without a Pringsheim assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growthrate-root"),
                DeclarationHandle.Create(Prefix + "growthRate_root"), H("growthRate_root"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), Equal(Multiply(Subtract(Num(2), Call("growthRate", F.Id("w"), F.Id("hw"))), Call("corrEval", F.Id("w"), Call("growthRate", F.Id("w"), F.Id("hw")))), Call("growthRate", F.Id("w"), F.Id("hw"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growthrate-gt-three-halves"),
                DeclarationHandle.Create(Prefix + "growthRate_gt_three_halves"), H("growthRate_gt_three_halves"),
                StatementSource.FromAuthor(Disp(All("w", Word(), AllProp("hw", NotEqual(F.Id("w"), Nil()), Imp(LeqF(Num(3), Qualified("List", "length", F.Id("w"))), LtF(new Formula.Fraction(Num(3), Num(2)), Call("growthRate", F.Id("w"), F.Id("hw")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For words of length at least three, a root lies strictly between 3/2 and 2. The convergent scalar counting identity excludes a larger reciprocal radius, placing the growth rate above that root."))), DescribeRole.Theorem))));

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
