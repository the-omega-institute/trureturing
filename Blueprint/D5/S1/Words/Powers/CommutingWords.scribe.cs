using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class CommutingWordsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/karhumaki2004words");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classify commuting finite words as natural powers of a common word.",
        H("Commuting Words and Common Powers"),
        Blocks(Describe.Lean(
            DescribeId.Create("commute-iff-common-power"),
            DeclarationHandle.Create(
                "D5/S1/Words/Powers/CommutingWords.commute_iff_common_power"),
            H("Full commutation classification"),
            StatementSource.FromAuthor(ClassificationFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "For every universe level ell, every alphabet type A in Type ell, and all "
                    + "finite words u and v over A, concatenation commutes exactly when both "
                    + "words are natural powers of one word w. The operation append is list "
                    + "concatenation, and wordPower(k,w) is the concatenation of k copies of w. "
                    + "The exponents m and n may be zero, and w may be empty. No finiteness "
                    + "or decidable equality assumption on A is required.")),
                Paragraph(Text(
                    "The forward implication uses induction on length(u)+length(v). If u is "
                    + "empty, take w=v with exponents 0 and 1; if v is empty, take w=u with "
                    + "exponents 1 and 0. Otherwise, splitting the equality of concatenations "
                    + "gives either v=append(u,r)=append(r,u), or the symmetric equations for u. "
                    + "The shorter pair therefore commutes and has smaller total length. "
                    + "Its common word also generates the original pair, by adding exponents. "
                    + "For the reverse implication, FreeMonoid.ofList identifies concatenation "
                    + "with multiplication and wordPower with natural monoid powers. "
                    + "Commute.pow_pow_self supplies commutation of these powers.")),
                Paragraph(Text(
                    "Section 3, Theorem 1(i)-(ii) of the cited report gives this classical "
                    + "equivalence and explicitly treats empty words. "
                    + "The source introduces finite alphabets; the statement here allows an "
                    + "arbitrary type. It asserts existence of a common word and exponents, "
                    + "without a primitive-root uniqueness or shortest-root conclusion."))),
            DescribeRole.Theorem))));

    private static Formula ClassificationFormula()
    {
        var alphabet = F.Id("A");
        var words = Call("List", alphabet);
        var u = F.Id("u");
        var v = F.Id("v");
        var w = F.Id("w");
        var m = F.Id("m");
        var n = F.Id("n");
        var powers = Bind(FormulaQuantifier.Exists, "w", words,
            Bind(FormulaQuantifier.Exists, "m", Naturals(),
                Bind(FormulaQuantifier.Exists, "n", Naturals(),
                    Logic(Equal(u, Call("wordPower", m, w)), FormulaLogicOperator.And,
                        Equal(v, Call("wordPower", n, w))))));
        var classification = Logic(
            Equal(Call("append", u, v), Call("append", v, u)),
            FormulaLogicOperator.Iff, powers);
        return Disp(Bind(FormulaQuantifier.ForAll, "ell", F.Id("Universe"),
            Bind(FormulaQuantifier.ForAll, "A", Call("Type", F.Id("ell")),
                Bind(FormulaQuantifier.ForAll, "u", words,
                    Bind(FormulaQuantifier.ForAll, "v", words, classification)))));
    }

    private static Formula Bind(
        FormulaQuantifier quantifier, string variable, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Logic(Formula left, FormulaLogicOperator operation, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), operation, Seq(Open, right, Close));
}
