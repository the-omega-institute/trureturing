using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DominatingSetAverageBoundStemDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stem blocks group a stem with all its leaf neighbours. The local counting estimate "
            + "is Lemma 2.6 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average "
            + "Order of Dominating Sets of a Graph, arXiv:2208.10475. Distinct blocks are "
            + "disjoint, with the two endpoint descriptions of a two-leaf component identified.",
        H("Stem-block counting for dominating sets"),
        Blocks(
            Node("block", "Stem block", "stemBlock", BlockFormula(),
                "The block is the stem together with all its leaf neighbours.", DescribeRole.Definition),
            Node("swap", "Stem substitution", "stemSwap", SwapFormula(),
                "Replace every selected leaf neighbour by the stem and a chosen subset of its leaves.",
                DescribeRole.Definition),
            Node("swap-dominates", "Substitution preserves domination", "stemSwap_dominating",
                SwapDominatesFormula(), "The inserted stem dominates all removed leaves. "
                    + "Any other vertex formerly dominated by a removed leaf is its stem.", DescribeRole.Theorem),
            Node("blocks", "Distinct stem blocks", "stemBlocks", BlocksFormula(),
                "Take the image of the stems under the block map. Equal two-vertex blocks occur once.",
                DescribeRole.Definition),
            Node("disjoint", "Distinct blocks are disjoint", "stemBlocks_pairwiseDisjoint",
                DisjointFormula(), "A leaf has only one neighbour. Overlapping blocks either have "
                    + "the same stem or are the same component consisting of two adjacent leaves.",
                DescribeRole.Theorem),
            Node("active", "Active dominating-set family", "activeStemFamily", ActiveFormula(),
                "Retain the dominating sets that do not contain the whole stem block.", DescribeRole.Definition),
            Node("local-bound", "Stem-block counting bound", "activeStemFamily_bound", BoundFormula(false),
                "Pair each dominating set omitting the stem with its replacement selecting the stem "
                    + "and no leaves. The original has k critical and one omitted block vertex; its "
                    + "replacement has one critical and k omitted block vertices. The injection "
                    + "cancels these contributions. Each remaining active set contains the stem "
                    + "and has one critical block vertex and at least one omitted leaf.", DescribeRole.Theorem),
            Node("local-strict", "Strictness for at least three leaves", "activeStemFamily_strict",
                BoundFormula(true), "Select every vertex except the stem, and substitute the stem "
                    + "together with one leaf. At least two leaves remain omitted and only the stem "
                    + "is critical in the block. This set cannot be an empty-leaf replacement, "
                    + "so its positive surplus remains after cancellation.", DescribeRole.Theorem),
            Node("local-equality", "Exact balance in star-like blocks", "activeStemFamily_eq_of_starLike",
                EqualityFormula(), "With one leaf every selected-stem active set has zero gap. "
                    + "With two leaves any selected-stem set omitting both leaves comes from an "
                    + "omitted-stem predecessor: replace the stem by its leaves. Every other "
                    + "neighbour is itself a stem and retains a leaf neighbour, so domination "
                    + "is preserved. The remaining sets have one omitted and one critical "
                    + "block vertex, giving equality.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("dominating-stem-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula SetOf(Formula variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, variable, Sp, InMacro, Sp, domain, Sp, Bar, Sp, predicate, CloseBrace);
    private static Formula Vertices(Formula body) =>
        All("V", Call("Type"), Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket,
            OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket,
            All("G", Call("SimpleGraph", F.Id("V")), body)));
    private static Formula Block(Formula s) => Call("stemBlock", F.Id("G"), s);
    private static Formula Leaves(Formula s) => Call("leafNeighbors", F.Id("G"), s);
    private static Formula Swap(Formula s, Formula a, Formula b) => Call("stemSwap", F.Id("G"), s, a, b);
    private static Formula Finsets() => Call("Finset", F.Id("V"));
    private static Formula Dominates(Formula a) => Call("IsDominating", F.Id("G"), a);
    private static Formula Active(Formula s) => Call("activeStemFamily", F.Id("G"), s);
    private static Formula Sum(Formula domain, Formula body) =>
        Seq(F.Sum, Underscore, OpenBrace, F.Id("S"), Sp, InMacro, Sp, domain, CloseBrace, Sp, body);

    private static Formula BlockFormula() => Disp(Vertices(All("s", F.Id("V"),
        Eq(Block(F.Id("s")), Call("insert", F.Id("s"), Leaves(F.Id("s")))))));
    private static Formula SwapFormula() => Disp(Vertices(All("s", F.Id("V"),
        All("S", Finsets(), All("T", Finsets(), Eq(Swap(F.Id("s"), F.Id("S"), F.Id("T")),
            Call("union", Call("insert", F.Id("s"), Call("sdiff", F.Id("S"), Leaves(F.Id("s")))),
                F.Id("T"))))))));
    private static Formula SwapDominatesFormula() => Disp(Vertices(All("s", F.Id("V"),
        All("S", Finsets(), All("T", Finsets(), Imp(Dominates(F.Id("S")),
            Dominates(Swap(F.Id("s"), F.Id("S"), F.Id("T")))))))));
    private static Formula BlocksFormula() => Disp(Vertices(Eq(Call("stemBlocks", F.Id("G")),
        Call("image", Call("stemBlock", F.Id("G")), SetOf(F.Id("s"), F.Id("V"),
            Call("Nonempty", Leaves(F.Id("s"))))))));
    private static Formula DisjointFormula() => Disp(Vertices(All("B", Finsets(), All("C", Finsets(),
        Imp(And(Member(F.Id("B"), Call("stemBlocks", F.Id("G"))),
                And(Member(F.Id("C"), Call("stemBlocks", F.Id("G"))), Ne(F.Id("B"), F.Id("C")))),
            Call("Disjoint", F.Id("B"), F.Id("C")))))));
    private static Formula ActiveFormula() => Disp(Vertices(All("s", F.Id("V"),
        Eq(Active(F.Id("s")), SetOf(F.Id("S"), Call("domSets", F.Id("G")),
            new Formula.Not(Subset(Block(F.Id("s")), F.Id("S"))))))));
    private static Formula EqualityFormula()
    {
        var s = F.Id("s"); var set = F.Id("S");
        var condition = new Formula.Logic(Eq(Call("leafCount", F.Id("G"), s), D(1)),
            FormulaLogicOperator.Or, Eq(Call("leafCount", F.Id("G"), s), D(2)));
        var critical = Sum(Active(s), Call("card", Call("inter",
            Call("criticalVertices", F.Id("G"), set), Block(s))));
        var omitted = Sum(Active(s), Call("card", Call("sdiff", Block(s), set)));
        return Disp(Vertices(All("s", F.Id("V"), Imp(Call("StarLike", F.Id("G")),
            Imp(condition, Eq(critical, omitted))))));
    }

    private static Formula BoundFormula(bool strict)
    {
        var s = F.Id("s"); var set = F.Id("S");
        var critical = Sum(Active(s), Call("card", Call("inter",
            Call("criticalVertices", F.Id("G"), set), Block(s))));
        var omitted = Sum(Active(s), Call("card", Call("sdiff", Block(s), set)));
        var assumption = strict ? Le(D(3), Call("leafCount", F.Id("G"), s))
            : Call("Nonempty", Leaves(s));
        return Disp(Vertices(All("s", F.Id("V"), Imp(assumption,
            strict ? Lt(critical, omitted) : Le(critical, omitted)))));
    }
}
