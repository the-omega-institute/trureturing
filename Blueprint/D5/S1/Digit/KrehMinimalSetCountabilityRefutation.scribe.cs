using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class KrehMinimalSetCountabilityRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/KrehMinimalSetCountabilityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/kreh2015minimalsets");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uncountably many infinite positive decimal-subsequence sets have first minimal-layer sizes 2 and 1.",
        H("Kreh's Minimal-Set Countability Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kreh-countability-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The asserted countability of the exceptional family"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(
                    F.Id("claim"), FormulaLogicOperator.Iff, CountabilityFormula()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the first sentence of Conjecture 18. Here N includes zero, "
                    + "and the explicit positivity condition restricts every member of M "
                    + "to Kreh's positive integers. Countable applies to the collection of "
                    + "sets M. The function eta(M,k) counts the minimal elements after k "
                    + "successive removals in the decimal-string subsequence order. It is "
                    + "the source's eta with superscript k; Definition 16 abbreviates "
                    + "eta(M,1) as eta(M). No computability or definability restriction is "
                    + "placed on M."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kreh-countability-claim-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The family is uncountable"),
                StatementSource.FromAuthor(Disp(new Formula.Not(CountabilityFormula()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Kreh's Theorem 14 and Examples 15 and 17 already supply the "
                        + "two-seed chain mechanism with minimal-layer sizes 2, 1, 1, and "
                        + "then 1 forever. The argument here makes an arbitrary-subset "
                        + "encoding explicit to deduce uncountability.")),
                    Paragraph(Text(
                        "For an arbitrary subset A of N, put u(j)=16*10^j. Let T(A) "
                        + "contain every u(2n) and also u(2n+1) exactly when n belongs "
                        + "to A, and put F(A)={1,6} union T(A). The printed digits of "
                        + "u(j) are 1 and 6 followed by j zeros. Thus u(i) is a decimal "
                        + "subsequence of u(j) exactly when i is at most j.")),
                    Paragraph(Text(
                        "The seeds 1 and 6 are incomparable, while 1 precedes every "
                        + "tail element. No tail element precedes either seed. Hence "
                        + "minimal(F(A))={1,6}; removing it leaves T(A). The mandatory "
                        + "element u(0)=16 precedes every element of T(A), so its "
                        + "minimal set is {16}. Both minimal sets are finite, and their "
                        + "cardinalities are exactly 2 and 1. The convention that ncard "
                        + "is zero on infinite sets plays no role.")),
                    Paragraph(Text(
                        "Every element is positive, and the injective map n to u(2n) "
                        + "proves that F(A) is infinite even when A is empty. Membership "
                        + "of u(2j+1) in F(A) recovers membership of j in A: such a "
                        + "value is neither a seed nor an even-indexed value. Therefore "
                        + "A to F(A) is injective on the entire powerset of N. If the "
                        + "displayed collection were countable, composing this injection "
                        + "with its natural-number encoding would contradict Cantor's "
                        + "theorem."))),
                DescribeRole.Theorem))));

    private static Formula CountabilityFormula()
    {
        Formula set = F.Id("M"), n = F.Id("n");
        Formula positive = new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), Naturals(),
            Parenthesized(new Formula.Logic(
                new Formula.Relation(n, FormulaRelationOperator.MemberOf, set),
                FormulaLogicOperator.Implies,
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n))));
        Formula inequality = new Formula.Relation(
            Call("eta", set, D(1)), FormulaRelationOperator.LessThanOrEqual,
            Call("eta", set, D(0)));
        Formula condition = And(positive, And(Call("Infinite", set), inequality));
        Formula family = Seq(
            OpenBrace, set, Sp, Subseteq, Sp, Naturals(), Sp, Mid, Sp,
            condition, CloseBrace);
        return Call("Countable", family);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula And(Formula left, Formula right) => new Formula.Logic(
        Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
