using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Forbidden;

internal sealed class BonaMagaRicheyHalfFrequencyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/bonamagarichey2026letter");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half letter frequency characterizes balanced borders of nonempty binary words.", H("BonaMagaRicheyHalfFrequency"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("claim"),
                StatementSource.FromAuthor(Disp(IffF(F.Id("claim"), All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), IffF(Call("Tendsto", Call("rho", F.Id("w")), F.Id("atTop"), Call("nhds", new Formula.Fraction(Num(1), Num(2)))), Call("BalancedBorders", F.Id("w")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("claim"), Paragraph(Text("The first sentence is encoded for every nonempty List Bool as convergence of the source averages to 1/2. No separate convergence hypothesis is added. The q sentence is outside this claim."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("result"),
                StatementSource.FromAuthor(Disp(All("w", Word(), Imp(NotEqual(F.Id("w"), Nil()), IffF(Call("Tendsto", Call("rho", F.Id("w")), F.Id("atTop"), Call("nhds", new Formula.Fraction(Num(1), Num(2)))), Call("BalancedBorders", F.Id("w"))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The half-frequency characterization holds for every nonempty binary word. For lengths at least three, the scalar moment identities and escaping Abel weights force the boundary signed moment to vanish. The longest-border estimate then forces every border to be balanced. Singleton and constant length-two words are excluded directly; mixed length-two words have balanced borders. The reverse implication gives exact half frequency at every positive length."))), DescribeRole.Theorem))));

    private static Formula Word() => Call("List", F.Id("Bool"));
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);


    private static Formula IffF(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);

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
