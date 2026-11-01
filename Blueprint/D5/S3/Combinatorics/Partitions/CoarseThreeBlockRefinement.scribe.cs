using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class CoarseThreeBlockRefinementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement counts between two- and three-block finite set partitions invert the upper-sum operator on coarse partitions and double the off-diagonal rank of symmetric binary matrices across bipartitions.",
        H("Coarse three-block partition refinements, triangular inversion, and bipartite masked ranks"),
        Blocks(
            Paragraph(Text("On the poset of set partitions of Fin q ordered by refinement (rho <= sigma when every block of rho lies in a block of sigma), the two-block and three-block strata form a two-step upper interval beneath the trivial one-block partition. Counting three-block refinements of each two-block partition expresses the unweighted sum over two- and three-block partitions as a linear combination of upper sums, proves triangular surjectivity of the refinement-transpose weight map, shows that upper sums on two- and three-block partitions determine all upper sums, and identifies the F2-rank of a bipartition-masked symmetric matrix as twice the rank of its off-diagonal rectangular block.")),
            Entry("party-partition", "PartyPartition", "Finite party partitions",
                All(V("q"), Nat,
                    Equal(Call("PartyPartition", V("q")),
                        Call("Finpartition", Typed(Call("univ"), Call("Finset", Fin(V("q"))))))),
                "A party partition of Fin q is a finite partition of Finset.univ into pairwise disjoint nonempty blocks whose union is all of Fin q, ordered by block refinement.",
                DescribeRole.Definition),
            Entry("partitions-of-card", "partitionsOfCard", "Stratum of k-block partitions",
                All(V("q"), Nat, All(V("k"), Nat,
                    Equal(Call("partitionsOfCard", V("q"), V("k")),
                        Call("filter", Typed(Call("univ"), Call("Finset", Call("PartyPartition", V("q")))),
                            Seq(Typed(Pi, Call("PartyPartition", V("q"))), Sp, Mapsto, Sp,
                                Equal(Call("card", Call("parts", Pi)), V("k"))))))),
                "Filters the finite set of all partitions of Fin q to those with exactly k nonempty blocks.",
                DescribeRole.Definition),
            Entry("two-or-three-partitions", "twoOrThreePartitions", "Coarse two- and three-block partitions",
                All(V("q"), Nat,
                    Equal(Call("twoOrThreePartitions", V("q")),
                        Seq(Call("partitionsOfCard", V("q"), D(2)), Sp, Cup, Sp, Call("partitionsOfCard", V("q"), D(3))))),
                "The union of the two-block and three-block partition strata of Fin q.",
                DescribeRole.Definition),
            Entry("nontrivial-partitions", "nontrivialPartitions", "Partitions with at least two blocks",
                All(V("q"), Nat,
                    Equal(Call("nontrivialPartitions", V("q")),
                        Call("filter", Typed(Call("univ"), Call("Finset", Call("PartyPartition", V("q")))),
                            Seq(Typed(Pi, Call("PartyPartition", V("q"))), Sp, Mapsto, Sp,
                                LeqRel(D(2), Call("card", Call("parts", Pi))))))),
                "Collects all partitions of Fin q having two or more blocks, excluding only the indiscrete one-block partition when q >= 1.",
                DescribeRole.Definition),
            Entry("part-of", "partOf", "Bundled block of an element",
                All(V("q"), Nat, All(Pi, Call("PartyPartition", V("q")), All(V("c"), Fin(V("q")),
                    Equal(Call("val", Typed(Call("partOf", Pi, V("c")), Call("parts", Pi))),
                        Call("part", Pi, V("c")))))),
                "Maps each element c in Fin q to the unique block of pi containing c, typed as a member of pi.parts.",
                DescribeRole.Definition),
            Entry("coarse-col", "coarseCol", "Coarse-grained colouring along a block listing",
                All(V("N"), Nat, All(V("q"), Nat, All(V("k"), Nat,
                    All(Pi, Call("PartyPartition", V("q")),
                        All(V("B"), Call("Equiv", Fin(V("k")), Call("parts", Pi)),
                            All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(V("u"), Fin(V("N")),
                                Equal(Call("coarseCol", Pi, V("B"), V("col"), V("u")),
                                    Call("symm", V("B"), Call("partOf", Pi, Apply(V("col"), V("u")))))))))))),
                "Composes a colouring col : Fin N to Fin q with the block map of pi and the inverse of an equivalence B : Fin k to pi.parts.",
                DescribeRole.Definition),
            Entry("masked-adj", "maskedAdj", "Partition-masked binary matrix",
                All(V("N"), Nat, All(V("q"), Nat, All(Gamma, BinMatrix,
                    All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(Pi, Call("PartyPartition", V("q")),
                        All(V("u"), Fin(V("N")), All(V("v"), Fin(V("N")),
                            Equal(Call("maskedAdj", Gamma, V("col"), Pi, V("u"), V("v")),
                                Call("ite",
                                    Equal(Call("part", Pi, Apply(V("col"), V("u"))), Call("part", Pi, Apply(V("col"), V("v")))),
                                    D(0), Apply(Gamma, V("u"), V("v"))))))))))),
                "Zeroes entries of Gamma whose row and column indices are assigned by col to the same block of pi, retaining entries across distinct blocks.",
                DescribeRole.Definition),
            Entry("partition-rank", "partitionRank", "Rank of the partition-masked matrix",
                All(V("N"), Nat, All(V("q"), Nat, All(Gamma, BinMatrix,
                    All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(Pi, Call("PartyPartition", V("q")),
                        Equal(Call("partitionRank", Gamma, V("col"), Pi),
                            Call("rank", Call("maskedAdj", Gamma, V("col"), Pi)))))))),
                "The matrix rank over ZMod 2 of maskedAdj(Gamma, col, pi).",
                DescribeRole.Definition),
            Entry("off-diag-block", "offDiagBlock", "Off-diagonal rectangular submatrix across two party subsets",
                All(V("N"), Nat, All(V("q"), Nat, All(Gamma, BinMatrix,
                    All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                        All(V("X"), Call("Finset", Fin(V("q"))), All(V("Y"), Call("Finset", Fin(V("q"))),
                            All(V("u"), SubtypeSet(V("x"), Fin(V("N")), Mem(Apply(V("col"), V("x")), V("X"))),
                                All(V("v"), SubtypeSet(V("y"), Fin(V("N")), Mem(Apply(V("col"), V("y")), V("Y"))),
                                    Equal(Call("offDiagBlock", Gamma, V("col"), V("X"), V("Y"), V("u"), V("v")),
                                        Apply(Gamma, Call("val", V("u")), Call("val", V("v")))))))))))),
                "Restricts Gamma to rows whose colour lies in X and columns whose colour lies in Y.",
                DescribeRole.Definition),
            Entry("upper-rank-sum", "upperRankSum", "Upper sum over two- and three-block coarsenings",
                All(V("q"), Nat, All(V("r"), Arrow(Call("PartyPartition", V("q")), Real),
                    All(Rho, Call("PartyPartition", V("q")),
                        Equal(Call("upperRankSum", V("r"), Rho),
                            SumOver(Conj(Mem(SigmaLower, Call("twoOrThreePartitions", V("q"))), LeqRel(Rho, SigmaLower)),
                                Apply(V("r"), SigmaLower)))))),
                "Sums a real-valued function r over all two- and three-block partitions sigma of Fin q refined by rho.",
                DescribeRole.Definition),
            Entry("coarse-weight", "coarseWeight", "Weighted refinement sum on a coarse partition",
                All(V("q"), Nat, All(V("c"), Arrow(Call("PartyPartition", V("q")), Real),
                    All(SigmaLower, Call("PartyPartition", V("q")),
                        Equal(Call("coarseWeight", V("c"), SigmaLower),
                            SumOver(Conj(Mem(Rho, Call("nontrivialPartitions", V("q"))), LeqRel(Rho, SigmaLower)),
                                Multiply(Pow(D(3), Difference(D(2), Typed(Call("card", Call("parts", Rho)), IntZ))),
                                    Apply(V("c"), Rho))))))),
                "Aggregates c(rho) weighted by the integer power 3^{2 - |rho|} over all partitions rho <= sigma with at least two blocks.",
                DescribeRole.Definition),
            Entry("stirling-refinement-count", "stirling_and_three_block_refinement_count",
                "Stirling identities, k-block partition cardinality, and three-block refinements of a bipartition",
                StirlingCountFormula(),
                "Establishes S(m, 2) = 2^{m-1} - 1 for m >= 1 and 2(S(q, 2) + S(q, 3)) = 3^{q-1} - 1 for q >= 1 by induction on the Stirling recurrence, proves |partitionsOfCard(q, k)| = S(q, k) by counting functions Fin q to Fin k fibrewise by kernel partition and injective block colouring against the falling-factorial power expansion, and proves that every two-block partition sigma = {X, Y} has S(|X|, 2) + S(|Y|, 2) = 2^{|X|-1} + 2^{|Y|-1} - 2 three-block refinements obtained by keeping one block intact and splitting the other into two nonempty parts.",
                DescribeRole.Theorem),
            Entry("upper-sum-inversion", "coarse_upper_sum_reduction_and_triangular_inversion",
                "Upper-sum reduction, poset Fubini identity, triangular surjectivity, and coarse determination",
                TriangularInversionFormula(),
                "For q >= 3, every three-block partition pi has upperRankSum(r, pi) = r(pi) + sum_{sigma in Pi_2(q), pi <= sigma} r(sigma) while every two-block partition sigma has upperRankSum(r, sigma) = r(sigma); exchanging the order of summation counts each two-block sigma once per three-block refinement, giving coefficient 1 - (2^{|X|-1} + 2^{|Y|-1} - 2) = 3 - 2^{|X|-1} - 2^{|Y|-1}. Exchanging summation over rho <= sigma yields the transpose identity pairing upperRankSum against coarseWeight. Because coarseWeight is triangular with nonzero diagonal entries 1 on Pi_2(q) and 1/3 on Pi_3(q), explicit back-substitution produces a preimage c supported on twoOrThreePartitions(q) for any target weight w, while matching upper sums on Pi_2(q) and Pi_3(q) uniquely determine r on twoOrThreePartitions(q) and hence upperRankSum(r, rho) for every partition rho.",
                DescribeRole.Theorem),
            Entry("bipartite-antidiagonal-rank", "bipartite_masked_antidiagonal_rank",
                "Rank doubling for symmetric matrices masked by a two-block partition",
                BipartiteRankFormula(),
                "For a symmetric matrix Gamma over ZMod 2 and a two-block partition sigma with distinct blocks X and Y, reindexing Fin N by the disjoint union of the X-coloured and Y-coloured coordinates conjugates maskedAdj(Gamma, col, sigma) to the block anti-diagonal matrix [[0, B], [B^T, 0]] where B = offDiagBlock(Gamma, col, X, Y). Its column space splits as the direct sum of range(B) and range(B^T), so rank(maskedAdj) = rank(B) + rank(B^T) = 2 rank(B).",
                DescribeRole.Theorem))));

    private static Formula StirlingCountFormula() => ConjAll(
        All(V("m"), Nat, Imp(LeqRel(D(1), V("m")),
            Equal(Call("stirlingSecond", V("m"), D(2)), Difference(Pow(D(2), Difference(V("m"), D(1))), D(1))))),
        All(V("q"), Nat, Imp(LeqRel(D(1), V("q")),
            ConjAll(
                Equal(Multiply(D(2), Parenthesized(Seq(Call("stirlingSecond", V("q"), D(2)), Sp, Plus, Sp, Call("stirlingSecond", V("q"), D(3))))),
                    Difference(Pow(D(3), Difference(V("q"), D(1))), D(1))),
                Equal(Fraction(Difference(Pow(Typed(D(3), Real), Difference(V("q"), D(1))), D(1)), D(2)),
                    Seq(Typed(Call("stirlingSecond", V("q"), D(2)), Real), Sp, Plus, Sp, Typed(Call("stirlingSecond", V("q"), D(3)), Real)))))),
        All(V("q"), Nat, All(V("k"), Nat,
            Equal(Call("card", Call("partitionsOfCard", V("q"), V("k"))), Call("stirlingSecond", V("q"), V("k"))))),
        All(V("q"), Nat, All(SigmaLower, Call("PartyPartition", V("q")),
            Imp(Mem(SigmaLower, Call("partitionsOfCard", V("q"), D(2))),
                Equal(Seq(Call("card", Call("filter", Call("partitionsOfCard", V("q"), D(3)),
                        Seq(Typed(Pi, Call("PartyPartition", V("q"))), Sp, Mapsto, Sp, LeqRel(Pi, SigmaLower)))), Sp, Plus, Sp, D(2)),
                    SumOver(Mem(V("B"), Call("parts", SigmaLower)), Pow(D(2), Difference(Call("card", V("B")), D(1)))))))));

    private static Formula TriangularInversionFormula() => ConjAll(
        All(V("q"), Nat, Imp(LeqRel(D(3), V("q")), All(V("r"), Arrow(Call("PartyPartition", V("q")), Real),
            Equal(SumOver(Mem(SigmaLower, Call("twoOrThreePartitions", V("q"))), Apply(V("r"), SigmaLower)),
                Seq(SumOver(Mem(Pi, Call("partitionsOfCard", V("q"), D(3))), Call("upperRankSum", V("r"), Pi)),
                    Sp, Plus, Sp,
                    SumOver(Mem(SigmaLower, Call("partitionsOfCard", V("q"), D(2))),
                        Multiply(Difference(D(3), SumOver(Mem(V("B"), Call("parts", SigmaLower)), Pow(D(2), Difference(Call("card", V("B")), D(1))))),
                            Call("upperRankSum", V("r"), SigmaLower)))))))),
        All(V("q"), Nat, All(V("c"), Arrow(Call("PartyPartition", V("q")), Real),
            All(V("r"), Arrow(Call("PartyPartition", V("q")), Real),
                Equal(SumOver(Mem(Rho, Call("nontrivialPartitions", V("q"))),
                        Multiply(Apply(V("c"), Rho), Parenthesized(Multiply(Pow(D(3), Difference(D(2), Typed(Call("card", Call("parts", Rho)), IntZ))),
                            Call("upperRankSum", V("r"), Rho))))),
                    SumOver(Mem(SigmaLower, Call("twoOrThreePartitions", V("q"))),
                        Multiply(Call("coarseWeight", V("c"), SigmaLower), Apply(V("r"), SigmaLower))))))),
        All(V("q"), Nat, All(V("w"), Arrow(Call("PartyPartition", V("q")), Real),
            Ex(V("c"), Arrow(Call("PartyPartition", V("q")), Real),
                ConjAll(
                    All(Rho, Call("PartyPartition", V("q")),
                        Imp(Seq(Neg, Parenthesized(Mem(Rho, Call("twoOrThreePartitions", V("q"))))),
                            Equal(Apply(V("c"), Rho), D(0)))),
                    All(SigmaLower, Call("PartyPartition", V("q")),
                        Imp(Mem(SigmaLower, Call("twoOrThreePartitions", V("q"))),
                            Equal(Call("coarseWeight", V("c"), SigmaLower), Apply(V("w"), SigmaLower)))))))),
        All(V("q"), Nat, All(V("rA"), Arrow(Call("PartyPartition", V("q")), Real),
            All(V("rB"), Arrow(Call("PartyPartition", V("q")), Real),
                ImpP(EqualOnTwoAndThree(V("rA"), V("rB")),
                    ConjAll(
                        All(SigmaLower, Call("PartyPartition", V("q")),
                            Imp(Mem(SigmaLower, Call("twoOrThreePartitions", V("q"))),
                                Equal(Apply(V("rA"), SigmaLower), Apply(V("rB"), SigmaLower)))),
                        All(Rho, Call("PartyPartition", V("q")),
                            Equal(Call("upperRankSum", V("rA"), Rho), Call("upperRankSum", V("rB"), Rho)))))))));

    private static Formula BipartiteRankFormula() => All(V("N"), Nat, All(V("q"), Nat,
        All(Gamma, BinMatrix,
            Imp(Call("IsSymm", Gamma), All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                All(SigmaLower, Call("PartyPartition", V("q")),
                    Imp(Mem(SigmaLower, Call("partitionsOfCard", V("q"), D(2))),
                        All(V("X"), Call("Finset", Fin(V("q"))), All(V("Y"), Call("Finset", Fin(V("q"))),
                            ImpP(ConjAll(Equal(Call("parts", SigmaLower), Call("pair", V("X"), V("Y"))), Seq(V("X"), Sp, Neq, Sp, V("Y"))),
                                Equal(Call("partitionRank", Gamma, V("col"), SigmaLower),
                                    Multiply(D(2), Call("rank", Call("offDiagBlock", Gamma, V("col"), V("X"), V("Y")))))))))))))));

    private static Formula EqualOnTwoAndThree(Formula rA, Formula rB) => ConjAll(
        All(SigmaLower, Call("PartyPartition", V("q")),
            Imp(Mem(SigmaLower, Call("partitionsOfCard", V("q"), D(2))),
                Equal(Call("upperRankSum", rA, SigmaLower), Call("upperRankSum", rB, SigmaLower)))),
        All(Pi, Call("PartyPartition", V("q")),
            Imp(Mem(Pi, Call("partitionsOfCard", V("q"), D(3))),
                Equal(Call("upperRankSum", rA, Pi), Call("upperRankSum", rB, Pi)))));

    private static Formula BinMatrix => Call("Matrix", Fin(V("N")), Fin(V("N")), Call("ZMod", D(2)));
    private static Formula SubtypeSet(Formula name, Formula type, Formula predicate) =>
        Seq(OpenBrace, name, Sp, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);

    private static DocumentBlock Entry(string id, string declaration, string title, Formula statement,
        string explanation, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula IntZ => Seq(Mathbb, Grp(V("Z")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula name, Formula type) => Parenthesized(Seq(name, Sp, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Ex(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeqRel(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, Parenthesized(b));
    private static Formula ImpP(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Rightarrow, Sp, Parenthesized(b));
    private static Formula Conj(Formula a, Formula b) => Seq(a, Sp, Land, Sp, Parenthesized(b));
    private static Formula ConjAll(params Formula[] items) =>
        Seq([.. items.SelectMany((x, i) => i == 0 ? new[] { Parenthesized(x) } : new[] { Sp, Land, Sp, Parenthesized(x) })]);
    private static Formula Multiply(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Difference(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Minus, Sp, b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumOver(Formula i, Formula x) => Seq(Sum, Underscore, Grp(i), Sp, x);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) =>
        Seq(f, Open, Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x })]), Close);
}
