using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class WordDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/Word.";
    private static readonly LibraryNoteRef Flp =
        LibraryNoteRef.Create("D5/L/Words/fridlabordepeltomaki2021automaticppl");
    private static readonly LibraryNoteRef Li =
        LibraryNoteRef.Create("D5/L/Words/li2020rulerperioddoubling");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal substitution fixed word agrees with positive-position valuation parity.",
        H("The Period-Doubling Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pd-word-pdmorphism"),
                DeclarationHandle.Create(Prefix + "pdMorphism"),
                H("The source substitution"),
                StatementSource.FromAuthor(MorphismFormula()),
                AssessedProvenance.FromLiterature(Flp),
                Blocks(Paragraph(Text("Section 5.1, printed page 12: “The period-doubling word u_pd is the 2-automatic word” u_pd = φ_pd^ω(a) = abaaabababaaabaa…, with φ_pd(a) = ab and φ_pd(b) = aa. Here a is false and b is true; the displayed list is that substitution literally."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pd-word-pdblock"),
                DeclarationHandle.Create(Prefix + "pdBlock"),
                H("Literal substitution approximants"),
                StatementSource.FromAuthor(BlockFormula()),
                AssessedProvenance.FromLiterature(Flp),
                Blocks(Paragraph(Text("The e-th approximant is the e-th morphism iterate of the one-letter word a. Iteration is the existing morphismPower operation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pd-word-u-pd"),
                DeclarationHandle.Create(Prefix + "u_pd"),
                H("The infinite fixed word"),
                StatementSource.FromAuthor(WordFormula()),
                AssessedProvenance.FromLiterature(Flp),
                Blocks(Paragraph(Text("Section 5.1, printed page 12: “The period-doubling word u_pd is the 2-automatic word” u_pd = φ_pd^ω(a) = abaaabababaaabaa…, with φ_pd(a) = ab and φ_pd(b) = aa. The zero-based n-th symbol is read from phi_pd^(n+1)(a); the block theorem proves that this position is covered and agrees with every longer approximant. getElemOption is optional list indexing and getD supplies its stated default."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pd-word-block-valuation"),
                DeclarationHandle.Create(Prefix + "block_valuation"),
                H("Every approximant has the valuation letters"),
                StatementSource.FromAuthor(ValuationFormula()),
                AssessedProvenance.FromLiterature(Li),
                Blocks(Paragraph(Text("Li, printed page 2: “The other one is the period-doubling sequence (A096268 in OEIS), which can be defined as the fixed point of the two substitution 0 → 01, 1 → 00 with initial word 0.” “We know that this sequence can also be defined as the sequence (a[n])ₙ∈ℕ⁺ modulo 2.” Positive position i+1 has symbol determined by v_2(i+1) modulo two. The theorem also proves the exact iterate length. mod is the natural-number remainder; decide converts a proposition to a Boolean."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Upd(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [n]);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula MorphismFormula() => Disp(All("b", Ty("Bool"),
        Eqn(Call("pdMorphism", V("b")), Seq(OpenBracket, Ty("false"), Comma,
            Call("not", V("b")), CloseBracket))));
    private static Formula BlockFormula() => Disp(All("e", N(),
        Eqn(Call("pdBlock", V("e")), Call("morphismPower", Ty("pdMorphism"), V("e"),
            Seq(OpenBracket, Ty("false"), CloseBracket)))));
    private static Formula WordFormula() => Disp(All("n", N(),
        Eqn(Upd(V("n")), Call("getD", Call("getElemOption",
            Call("pdBlock", Add(V("n"), D(1))), V("n")), Ty("false")))));
    private static Formula ValuationFormula() => Disp(All("e", N(), And(
        Eqn(Call("length", Call("pdBlock", V("e"))), Pow(D(2), V("e"))),
        All("i", N(), Imp(LtF(V("i"), Pow(D(2), V("e"))),
            Eqn(Call("getElemOption", Call("pdBlock", V("e")), V("i")),
                Call("some", Call("decide", Eqn(Call("mod",
                    Call("padicValNat", D(2), Add(V("i"), D(1))), D(2)), D(1))))))))));

}
