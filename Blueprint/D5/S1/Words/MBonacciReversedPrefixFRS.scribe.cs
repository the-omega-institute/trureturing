using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class MBonacciReversedPrefixFRSDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/MBonacciReversedPrefixFRS.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reverse of every natural-start prefix of the literal m-bonacci word is an actual "
            + "fully right-special factor.",
        H("Reversed Prefixes Are Fully Right-Special"),
        Blocks(
            Paragraph(Text(
                "For every natural order m at least two, write word, Occ and FRS for the "
                + "literal m-bonacci word and its predicates at that order. For every natural "
                + "length ell, include its position-zero prefix. The factor is "
                + "taken at a natural start and then reversed; occurrence starts remain natural "
                + "and may depend on the appended letter.")),
            Describe.Lean(
                DescribeId.Create("reversed-prefix-fully-right-special"),
                DeclarationHandle.Create(Prefix + "reversed_prefix_fully_right_special"),
                H("Every reversed prefix is fully right-special"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof constructs sentinel iterates T repeatedly from the empty source. "
                    + "Public actual-word laws transport their occurrence at zero and strict "
                    + "boundary growth gives ell at most the iterate length. The literal images "
                    + "make every sentinel iterate palindromic. Its suffix of length ell is the "
                    + "reversed prefix, and dropping the common prefix from each actual right "
                    + "extension preserves a natural-start occurrence of the reversed suffix."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The result covers ell equal to zero and m equal to two. The relation between "
                + "the Parikh-vector cardinality of all factors of a given length and greedy "
                + "numeration digits requires further results.")))));

    private static Formula Statement()
    {
        Formula r = Reverse(Factor(D(0), F.Id("ell")));
        return Disp(All("m", N(), Imp(
            Leq(D(2), F.Id("m")),
            All("ell", N(), Conj(
                Eq(Len(r), F.Id("ell")),
                And(
                    Ex("q", N(), Occ(r, F.Id("q"))),
                    Call("FRS", r)))))));
    }

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Factor(Formula start, Formula length) =>
        Call("factor", F.Id("word"), start, length);
    private static Formula Reverse(Formula s) => Call("reverse", s);
    private static Formula Len(Formula s) => Call("length", s);
    private static Formula Occ(Formula s, Formula q) => Call("Occ", s, q);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Conj(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
