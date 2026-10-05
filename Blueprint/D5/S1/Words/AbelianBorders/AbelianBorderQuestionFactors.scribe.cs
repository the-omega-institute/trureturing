using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AbelianBorders;

internal sealed class AbelianBorderQuestionFactorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AbelianBorders/AbelianBorderQuestionFactors.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/charlier2015abelianbordered");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square gaps yield infinitely many nonempty weakly abelian unbordered factors.",
        H("An Unbounded Family of Unbordered Factors"),
        Blocks(
            Node("unbordered-factor-family", "The factor family 12 A to the power m 0", "F",
                FFormula(),
                "The word F(m) is 12 followed by m copies of A and a final 0. Its length is 15m+3, and "
                    + "each letter occurs 5m+1 times.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("unbordered-family", "Every word in the family is unbordered", "unbordered",
                UnborderedFormula(),
                "Equal prefix and suffix frequencies would force a positive weighted sum of two internal "
                    + "projected cut vectors to be zero. The only possible pair of cut residues forces equal "
                    + "prefix and suffix lengths, but those residues are incompatible with the total length "
                    + "15m+3. The end cases also exclude a whole-word suffix.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("infinitely-many-unbordered-factors", "Infinitely many unbordered factors", "infinitely_many_unbordered",
                InfinitelyManyUnborderedFormula(),
                "Between the square block indices q squared and (q+1) squared there are exactly 2q copies "
                    + "of A. The last two letters of the first B, these copies of A, and the first letter of "
                    + "the next B give F(2q) as a factor. These nonempty unbordered factors have lengths 30q+3, "
                    + "which are unbounded.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula FFormula() =>
        Disp(ForAll("m", F.Id("Nat"), Equal(Call("F", F.Id("m")), Call("append", Call("append", Seq(OpenBracket,
                                D(1), Comma, Sp, D(2), CloseBracket), Call("flatten", Call("replicate",
                                    F.Id("m"), F.Id("A")))), Seq(OpenBracket, D(0), CloseBracket)))));

    private static Formula UnborderedFormula() =>
        Disp(ForAll("m", F.Id("Nat"), Negated(Call("WeakAbelianBordered", Call("F", F.Id("m"))))));

    private static Formula InfinitelyManyUnborderedFormula() =>
        Disp(Negated(Call("Finite", Seq(OpenBrace, Sp, F.Id("u"), Colon, Sp, Call("List", Call("Fin",
                                D(3))), Sp, Mid, Sp, And(ThereExists("i", F.Id("Nat"), ThereExists("n",
                                    F.Id("Nat"), Equal(F.Id("u"), Call("factor", F.Id("word"), F.Id("i"),
                                            F.Id("n"))))), And(NotEqual(F.Id("u"), Seq(OpenBracket,
                                        CloseBracket)), Negated(Call("WeakAbelianBordered", F.Id("u"))))),
                        CloseBrace, Sp))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ThereExists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Negated(Formula value) => new Formula.Not(Seq(Open, value, Close));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
