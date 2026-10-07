using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AbelianBorders;

internal sealed class AbelianBorderQuestionWordDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/charlier2015abelianbordered");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced blocks at square indices define an infinite ternary word.",
        H("A Ternary Word with Square Markers"),
        Blocks(
            Node("long-balanced-block", "The balanced excursion A", "A",
                AFormula(),
                "The block A is 110022222000111. Its length is fifteen, and each of the three letters "
                    + "occurs five times.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("short-balanced-block", "The balanced block B", "B",
                BFormula(),
                "The block B is 012. Each of the three letters occurs once.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("square-indexed-blocks", "Blocks selected by square indices", "block",
                BlockFormula(),
                "At every square index j the block is B; at all other indices it is A. Zero is a square index.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("initial-concatenation", "Finite initial concatenations", "initial",
                InitialFormula(),
                "The initial concatenation of zero blocks is empty. Each succeeding concatenation appends "
                    + "the block at the next index.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("infinite-ternary-word", "The infinite ternary word", "word",
                WordFormula(),
                "The letter at position n is read from initial(n+1), with zero as the default value. Each "
                    + "block has at least three letters, so position n lies within this concatenation. The "
                    + "resulting word is the concatenation of all the blocks.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("word-prefixes-and-periodicity", "Prefixes and bounded weak abelian periodicity", "word_structure",
                WordStructureFormula(),
                "Prefixes agree with the finite block concatenations, and every initial concatenation has "
                    + "equal counts of all three letters. Cuts at the block boundaries give a strictly "
                    + "increasing decomposition with block lengths at most fifteen and common frequencies "
                    + "(1/3,1/3,1/3).",
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

    private static Formula AFormula() =>
        Disp(Equal(F.Id("A"), Seq(OpenBracket, D(1), Comma, Sp, D(1), Comma, Sp, D(0), Comma, Sp,
                    D(0), Comma, Sp, D(2), Comma, Sp, D(2), Comma, Sp, D(2), Comma, Sp, D(2), Comma,
                    Sp, D(2), Comma, Sp, D(0), Comma, Sp, D(0), Comma, Sp, D(0), Comma, Sp, D(1),
                    Comma, Sp, D(1), Comma, Sp, D(1), CloseBracket)));

    private static Formula BFormula() =>
        Disp(Equal(F.Id("B"), Seq(OpenBracket, D(0), Comma, Sp, D(1), Comma, Sp, D(2), CloseBracket)));

    private static Formula BlockFormula() =>
        Disp(ForAll("j", F.Id("Nat"), Equal(Call("block", F.Id("j")), Call("ite", Call("IsSquare",
                            F.Id("j")), F.Id("B"), F.Id("A")))));

    private static Formula InitialFormula() =>
        Disp(And(Equal(Call("initial", D(0)), Seq(OpenBracket, CloseBracket)), ForAll("j", F.Id("Nat"),
                    Equal(Call("initial", Add(F.Id("j"), D(1))), Call("append", Call("initial", F.Id("j")),
                            Call("block", F.Id("j")))))));

    private static Formula WordFormula() =>
        Disp(ForAll("n", F.Id("Nat"), Equal(Call("word", F.Id("n")), Call("getD", Call("initial",
                            Add(F.Id("n"), D(1))), F.Id("n"), D(0)))));

    private static Formula WordStructureFormula() =>
        Disp(And(ForAll("j", F.Id("Nat"), ForAll("r", F.Id("Nat"), Implies(LessOrEqual(F.Id("r"),
                                Call("length", Call("block", F.Id("j")))), Equal(Call("factor", F.Id("word"),
                                    D(0), Add(Call("length", Call("initial", F.Id("j"))), F.Id("r"))),
                                Call("append", Call("initial", F.Id("j")), Call("take", F.Id("r"),
                                        Call("block", F.Id("j")))))))), And(ForAll("j", F.Id("Nat"),
                        ForAll("a", Call("Fin", D(3)), Equal(Call("count", Call("initial", F.Id("j")),
                                    F.Id("a")), Call("count", Call("initial", F.Id("j")), D(0))))),
                    Call("BoundedWeakAbelianPeriodic", F.Id("word")))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
}
