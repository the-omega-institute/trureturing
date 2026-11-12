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
                    "Here NatCard(G) is the order Nat.card(G) of G, card(t) is the number of labels "
                    + "in t, and sum(t,a) is the sum of a(i) over i in t. Support means the chosen "
                    + "finite label set s; it may contain labels whose value under a is zero.")),
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
                    "Fin m is the type of natural numbers j with j < m. The expression "
                    + "biUnion(univ(Fin m),B) is the union of B(j) over all m indices j in Fin m.")),
                    Paragraph(Text(
                    "For m=0 the cardinality equation forces an empty support. For one block use "
                    + "the whole remaining support. With at least two blocks, the extraction theorem "
                    + "removes one zero-sum block and recursion applies to the exact complement. "
                    + "The complement retains both the required cardinality and zero total. Fin.cons "
                    + "adjoins the removed block, preserving the exact Fin m endpoint and the same "
                    + "original label support. This is the iterated consequence of the cited theorem "
                    + "needed for the finite-abelian subgroup partition criterion.")),
                    Paragraph(Text(
                    "For the subgroup application, let K be any finite group, H an abelian subgroup, "
                    + "h its order, and pi the projection from K to its abelianization. For every "
                    + "positive integer m, there exists an H-supported multiset A of size mh with "
                    + "projected product one and no partition into m product-one blocks of size h "
                    + "if and only if H intersects the commutator subgroup of K nontrivially. Here "
                    + "a partition consists of multisets C(j) in K indexed by Fin m, with their "
                    + "multiset sum exactly A; each C(j) has cardinality h and an enumerating list "
                    + "whose product in K is one. K itself need not be abelian, and repeated values "
                    + "and the trivial subgroup remain in scope.")),
                    Paragraph(Text(
                    "When the intersection is trivial, lift A to a multiset in H. Its product lies "
                    + "in the intersection because the kernel of pi is the commutator subgroup, "
                    + "so that product is one. Label each occurrence separately by its value in H "
                    + "and an occurrence number, using Multiset.toEnumFinset. Apply "
                    + "exists_zero_sum_partition to Additive H with these same labels. The exact "
                    + "union and disjointness transport to the literal multiset sum of the blocks; "
                    + "their cardinalities and list products transport along the subgroup inclusion. "
                    + "Thus projected product one supplies the required actual partition.")),
                    Paragraph(Text(
                    "For the converse, take a nonidentity element a in the intersection once and "
                    + "mh minus one copies of the identity. Every projected entry is one. A proposed "
                    + "partition would contain a exactly once in total. Each block contains either "
                    + "zero or one copies of a, and all its other entries are identities; its list "
                    + "product is therefore one or a respectively. Product one in every block "
                    + "forces zero copies in every block, contradicting the exact multiset sum.")),
                    Paragraph(Text(
                    "Taking m to be the index of H gives total length equal to the order of K. "
                    + "In every finite nonabelian K choose one nonidentity commutator element a "
                    + "and fix H to be the cyclic subgroup generated by a. This single abelian H "
                    + "then supports such an obstruction for every positive m, including m=1. "
                    + "This is the subgroup criterion in Ma and Zhang, Aliabadi's Problems 7.4 and "
                    + "7.6: Two-letter and subgroup extensions, Proposition in The subgroup question. "
                    + "It is an application of the existing zero-sum partition theorem and "
                    + "abelianization and multiset laws, with no claim to a new general theorem "
                    + "or literature priority."))),
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
        All("G", F.Id("Typeu"), Seq(
            OpenBracket, Call("AddCommGroup", G), CloseBracket, Sp,
            OpenBracket, Call("Finite", G), CloseBracket, Sp,
            All("I", F.Id("Typev"),
                All("a", Arrow(I, G), All("s", Call("Finset", I), body)))));

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
