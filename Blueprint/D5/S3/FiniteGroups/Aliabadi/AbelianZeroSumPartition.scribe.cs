using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Aliabadi;

internal sealed class AbelianZeroSumPartitionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/Aliabadi/AbelianZeroSumPartition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/erdos1961ginzburgziv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite abelian zero-sum extraction and exact partitions preserve the original label support.",
        H("Finite abelian Erdős–Ginzburg–Ziv extraction and partitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-abelian-egz-original-labels"),
                DeclarationHandle.Create(Owner + "exists_zero_sum_card"),
                H("Order-length extraction in every finite abelian group"),
                StatementSource.FromAuthor(Disp(Extraction())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "G and the label type I inhabit independent universes u and v. G is an additive "
                    + "commutative group with a Finite instance; I need not be finite. For any labeling "
                    + "a and finite support s with at least 2 Nat.card(G) minus 1 labels, a subset of "
                    + "exactly Nat.card(G) original labels has zero sum. Values may repeat, and the "
                    + "trivial group is included.")),
                    Paragraph(Text(
                    "The cyclic seed is Mathlib's ZMod.erdos_ginzburg_ziv. For a direct product, "
                    + "greedy extraction builds 2q minus 1 pairwise disjoint first-coordinate "
                    + "zero-sum blocks of size n in the exact unused support. Apply second-factor "
                    + "extraction to the second-coordinate sums of these same blocks and union the "
                    + "q selected blocks. Disjointness gives nq original labels. Induction over "
                    + "Gordon.Chain and Gordon.finite_abelian_presentation supplies arbitrary finite "
                    + "abelian groups, and the additive equivalence transports sums without relabeling. "
                    + "The arbitrary finite abelian theorem is stated in the primary article's final paragraph."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-abelian-zero-sum-exact-partition"),
                DeclarationHandle.Create(Owner + "exists_zero_sum_partition"),
                H("Exactly m zero-sum blocks on the original labels"),
                StatementSource.FromAuthor(Disp(Partition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "If the original support has cardinality m Nat.card(G) and total zero, there is "
                    + "a function B from Fin m to Finset I. Each B(j) is a subset of s, distinct "
                    + "indices have disjoint blocks, the union over all indices equals s, and every "
                    + "block has cardinality Nat.card(G) and sum zero. There is no cyclicity, "
                    + "distinct-value, nontriviality, extraction-certificate or Fintype(I) hypothesis.")),
                    Paragraph(Text(
                    "For m=0 the cardinality equation forces an empty support. For one block use "
                    + "the whole remaining support. With at least two blocks, the extraction theorem "
                    + "removes one zero-sum block and recursion applies to the exact complement. "
                    + "The complement retains both the required cardinality and zero total. Fin.cons "
                    + "adjoins the removed block, preserving the exact Fin m endpoint and the same "
                    + "original label support. This is the iterated consequence of the cited theorem "
                    + "needed for the finite-abelian subgroup partition criterion."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula G => F.Id("G");
    private static Formula I => F.Id("I");
    private static Formula A => F.Id("a");
    private static Formula S => F.Id("s");
    private static Formula Order => Call("NatCard", G);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Sum(Formula s) => Call("sum", s, A);
    private static Formula Base(Formula body) =>
        All("G", F.Id("Typeu"), All("group", Call("AddCommGroup", G),
            All("finite", Call("Finite", G), All("I", F.Id("Typev"),
                All("a", Arrow(I, G), All("s", Call("Finset", I), body))))));

    private static Formula Extraction()
    {
        var t = F.Id("t");
        return Base(Imp(Le(Seq(D(2), Cdot, Order, Minus, D(1)), Card(S)),
            Ex("t", Call("Finset", I), And(Subset(t, S),
                And(Eq(Card(t), Order), Eq(Sum(t), D(0)))))));
    }

    private static Formula Partition()
    {
        var m = F.Id("m"); var b = F.Id("B"); var j = F.Id("j"); var k = F.Id("k");
        var fin = Call("Fin", m); var bj = Call("B", j); var bk = Call("B", k);
        return Base(All("m", N,
            Imp(And(Eq(Card(S), Seq(m, Cdot, Order)), Eq(Sum(S), D(0))),
                Ex("B", Arrow(fin, Call("Finset", I)),
                    And(All("j", fin, Subset(bj, S)),
                        And(All("j", fin, All("k", fin,
                            Imp(new Formula.Not(Eq(j, k)), Call("Disjoint", bj, bk)))),
                            And(Eq(Call("biUnion", Call("univ", fin), b), S),
                                And(All("j", fin, Eq(Card(bj), Order)),
                                    All("j", fin, Eq(Sum(bj), D(0)))))))))));
    }
}
