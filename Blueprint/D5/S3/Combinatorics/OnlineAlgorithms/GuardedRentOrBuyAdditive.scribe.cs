using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OnlineAlgorithms;

internal sealed class GuardedRentOrBuyAdditiveDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Computability/schiavo2026repeatedrentorbuy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant-block cost comparison for the guarded rule.",
        H("Additive comparison on constant blocks"),
        Blocks(
            Node("block", "Schedule at a constant rate", DescribeRole.Definition,
                "Map each Boolean action to a pair of the fixed real rate and that action."),
            Node("single_block_bound", "One reset price of excess from zero rule carry", DescribeRole.Theorem,
                "Start the rule with zero carry and rent accumulator, with the first action governed by "
                + "the ordinary threshold. The comparator may start with any nonnegative carry. For positive "
                + "rates, telescope the first-crossing and minimum-cost potentials from Schiavo's Proposition 6 "
                + "and Lemmas 7–8. A zero-rate block with zero rule carry has zero rule cost."),
            Node("two_block_bound", "Two reset prices of excess over two constant blocks", DescribeRole.Theorem,
                "The two real rates are nonnegative and either action block can be empty. With an increase, "
                + "the ordered-crossing polynomial estimate bounds the rule's change of potential. With a "
                + "guarded decrease, reset at the drop and use the monotonicity of the comparator potential "
                + "from Lemma 14. With a decrease before any crossing, compare costs through the first ordinary "
                + "reset and apply the one-block bound to the remaining suffix. If no crossing occurs, the "
                + "unfinished-cycle comparison suffices."))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string explanation) =>
        Describe.Lean(
            DescribeId.Create("guarded-additive-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name),
            H(title),
            StatementSource.FromAuthor(FormulaFor(name)),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(explanation))),
            role);

    private static Formula FormulaFor(string name) => name switch
    {
        "block" => Disp(Seq(
            Forall, Sp, Open, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Open, F.Id("rs"),
            Colon, Sp, F.Id("List"), Open, F.Id("Bool"), Close, Close, Comma, Sp, F.Id("block"), Open,
            F.Id("a"), Comma, Sp, F.Id("rs"), Close, Eq, F.Id("map"), Open, F.Id("r"), Mapsto, Sp, Open,
            F.Id("a"), Comma, Sp, F.Id("r"), Close, Comma, Sp, F.Id("rs"), Close)),
        "single_block_bound" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Sp, F.Id("o"), Colon, Sp, Seq(Mathbb,
            Grp(F.Id("R"))), Close,
            Open, F.Id("s"), Colon, Sp, F.Id("State"), Close, Open, F.Id("rs"), Colon, Sp, F.Id("List"), Open,
            F.Id("Bool"), Close, Close, Comma, Sp, Open, D(0), Lt, F.Id("K"), Land, Sp, D(0), Le, Sp, F.Id("a"),
            Land, Sp, D(0), Le, Sp, F.Id("o"), Land, Sp, F.Id("carry"), Open, F.Id("s"), Close, Eq, D(0), Land, Sp, F.Id("acc"), Open, F.Id("s"), Close, Eq, D(0), Land, Sp, F.Id("reset"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Eq, F.Id("decide"), Open, F.Id("crossing"), Open,
            F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("a"), Close, Close, Close, Rightarrow, Sp, F.Id("policyCost"), Open, F.Id("K"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("replicate"), Open,
            F.Id("length"), Open, F.Id("rs"), Close, Comma, Sp, F.Id("a"), Close, Close, Le, Sp, F.Id("comparatorCost"), Open, F.Id("K"), Comma, Sp, F.Id("o"), Comma, Sp, F.Id("block"), Open,
            F.Id("a"), Comma, Sp, F.Id("rs"), Close, Close, Plus, F.Id("K"))),
        "two_block_bound" => Disp(Seq(
            Forall, Sp, Open, F.Id("K"), Sp, F.Id("a"), Sp, F.Id("b"), Colon, Sp, Seq(Mathbb,
            Grp(F.Id("R"))), Close,
            Open, F.Id("rs"), Sp, F.Id("ss"), Colon, Sp, F.Id("List"), Open, F.Id("Bool"), Close, Close, Comma, Sp, Open, D(0), Lt, F.Id("K"), Land, Sp, D(0), Le, Sp, F.Id("a"), Land, Sp, D(0), Le, Sp, F.Id("b"), Close,
            Rightarrow, Sp, F.Id("policyCost"), Open, F.Id("K"), Comma, Sp, F.Id("initial"), Comma, Sp, F.Id("append"), Open, F.Id("replicate"), Open, F.Id("length"), Open, F.Id("rs"), Close,
            Comma, Sp, F.Id("a"), Close, Comma, Sp, F.Id("replicate"), Open, F.Id("length"), Open, F.Id("ss"),
            Close, Comma, Sp, F.Id("b"), Close, Close, Close, Le, Sp, F.Id("comparatorCost"), Open, F.Id("K"),
            Comma, Sp, D(0), Comma, Sp, F.Id("append"), Open, F.Id("block"), Open, F.Id("a"), Comma, Sp, F.Id("rs"), Close, Comma, Sp, F.Id("block"), Open, F.Id("b"), Comma, Sp, F.Id("ss"), Close, Close,
            Close, Plus, D(2), Cdot, Sp, F.Id("K"))),
        _ => throw new ArgumentOutOfRangeException(nameof(name)),
    };
}
