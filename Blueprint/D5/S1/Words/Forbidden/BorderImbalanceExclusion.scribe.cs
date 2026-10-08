using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Forbidden;

internal sealed class BorderImbalanceExclusionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Forbidden/BorderImbalanceExclusion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/bonamagarichey2026letter");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The longest nonzero border imbalance excludes cancellation at the growth root.", H("BorderImbalanceExclusion"),
        Blocks(
            Describe.Lean(DescribeId.Create("signedcoeff"),
                DeclarationHandle.Create(Prefix + "signedCoeff"), H("signedCoeff"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("j", N(), Equal(Call("signedCoeff", F.Id("w"), F.Id("j")), IfF(Member(F.Id("j"), Call("borderLengths", F.Id("w"))), Cast(Call("imbalance", F.Id("w"), F.Id("j")), R()), Num(0))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("correval"),
                DeclarationHandle.Create(Prefix + "corrEval"), H("corrEval"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("corrEval", F.Id("w"), F.Id("x")), SumOver("j", Call("borderLengths", F.Id("w")), Pow(F.Id("x"), F.Id("j")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("heval"),
                DeclarationHandle.Create(Prefix + "hEval"), H("hEval"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("hEval", F.Id("w"), F.Id("x")), SumOver("j", Qualified("Finset", "range", Add(Qualified("List", "length", F.Id("w")), Num(1))), Multiply(Call("signedCoeff", F.Id("w"), F.Id("j")), Pow(F.Id("x"), F.Id("j"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("balanced-iff-imbalance-zero"),
                DeclarationHandle.Create(Prefix + "balanced_iff_imbalance_zero"), H("balanced_iff_imbalance_zero"),
                StatementSource.FromAuthor(Disp(All("w", Word(), IffF(Call("BalancedBorders", F.Id("w")), All("j", N(), Imp(Member(F.Id("j"), Call("borderLengths", F.Id("w"))), Equal(Call("imbalance", F.Id("w"), F.Id("j")), Num(0)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("correval-ge-full"),
                DeclarationHandle.Create(Prefix + "corrEval_ge_full"), H("corrEval_ge_full"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Imp(NotEqual(F.Id("w"), Nil()), Imp(LeqF(Num(0), F.Id("x")), LeqF(Pow(F.Id("x"), Qualified("List", "length", F.Id("w"))), Call("corrEval", F.Id("w"), F.Id("x"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("root-equation-envelope"),
                DeclarationHandle.Create(Prefix + "root_equation_envelope"), H("root_equation_envelope"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Imp(NotEqual(F.Id("w"), Nil()), Imp(LtF(Num(1), F.Id("x")), Imp(LtF(F.Id("x"), Num(2)), Imp(Equal(Multiply(Subtract(Num(2), F.Id("x")), Call("corrEval", F.Id("w"), F.Id("x"))), F.Id("x")), LeqF(Multiply(Subtract(Num(2), F.Id("x")), Pow(F.Id("x"), Qualified("Nat", "sub", Qualified("List", "length", F.Id("w")), Num(1)))), Num(1)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full-word border contributes x raised to the word length to the correlation sum. Positivity of all border contributions gives the displayed root envelope."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("heval-eq-border-sum"),
                DeclarationHandle.Create(Prefix + "hEval_eq_border_sum"), H("hEval_eq_border_sum"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Equal(Call("hEval", F.Id("w"), F.Id("x")), SumOver("j", Call("borderLengths", F.Id("w")), Multiply(Cast(Call("imbalance", F.Id("w"), F.Id("j")), R()), Pow(F.Id("x"), F.Id("j"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flip-flip"),
                DeclarationHandle.Create(Prefix + "flip_flip"), H("flip_flip"),
                StatementSource.FromAuthor(Disp(All("u", Word(), Equal(Qualified("List", "map", Qualified("Bool", "not"), Qualified("List", "map", Qualified("Bool", "not"), F.Id("u"))), F.Id("u"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flip-infix-iff"),
                DeclarationHandle.Create(Prefix + "flip_infix_iff"), H("flip_infix_iff"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("u", Word(), IffF(Qualified("List", "IsInfix", Qualified("List", "map", Qualified("Bool", "not"), F.Id("w")), Qualified("List", "map", Qualified("Bool", "not"), F.Id("u"))), Qualified("List", "IsInfix", F.Id("w"), F.Id("u"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-flip"),
                DeclarationHandle.Create(Prefix + "count_flip"), H("count_flip"),
                StatementSource.FromAuthor(Disp(All("u", Word(), Equal(Qualified("List", "count", F.Id("true"), Qualified("List", "map", Qualified("Bool", "not"), F.Id("u"))), Qualified("List", "count", F.Id("false"), F.Id("u")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unbalanced-heval-ne-zero"),
                DeclarationHandle.Create(Prefix + "unbalanced_hEval_ne_zero"), H("unbalanced_hEval_ne_zero"),
                StatementSource.FromAuthor(Disp(All("w", Word(), All("x", R(), Imp(new Formula.Not(Call("BalancedBorders", F.Id("w"))), Imp(LtF(Num(1), F.Id("x")), Imp(LtF(F.Id("x"), Num(2)), Imp(LeqF(Multiply(Subtract(Num(2), F.Id("x")), Pow(F.Id("x"), Qualified("Nat", "sub", Qualified("List", "length", F.Id("w")), Num(1)))), Num(1)), NotEqual(Call("hEval", F.Id("w"), F.Id("x")), Num(0)))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Choose the longest border whose imbalance is nonzero and complement the bits to make its imbalance positive. Prefix count differences bound every shorter coefficient. The resulting lower polynomial is strictly positive under the root envelope, so mixed positive and negative border biases cannot cancel."))), DescribeRole.Theorem))));

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

    private static Formula IfF(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(F.Id("ite")), Parenthesized(Seq(condition, Comma, yes, Comma, no)));

}
