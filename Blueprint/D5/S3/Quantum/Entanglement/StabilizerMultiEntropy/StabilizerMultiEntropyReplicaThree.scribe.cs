using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class StabilizerMultiEntropyReplicaThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/akella2026genuine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The replica-three multi-entropy of any normalized pure qubit stabilizer state reduces explicitly to its two- and three-party coarse-grainings, satisfies a refinement-weight vanishing criterion, and is determined across all nontrivial coarsenings by two- and three-party coarse data.",
        H("Reduction, vanishing criterion, and coarse determination of replica-three stabilizer multi-entropy"),
        Blocks(
            Paragraph(Text("Combining the coarse-partition rank sum for replica-three stabilizer multi-entropies with the upper-sum inversion on the set-partition poset expresses S_3^{(q)} for every q >= 3 through two- and three-party coarse-grained multi-entropies with integer power scaling 3^{2 - q}, expands arbitrary linear combinations over nontrivial coarsenings as coarse-weighted rank sums, and shows that agreeing two- and three-party coarse data determine all coarse-grained replica-three multi-entropies even between states on different numbers of qubits. Akella and Gadde, arXiv:2610.27080v1 Section II Eqs. (7)-(9) and Appendix A, establish the underlying odd-replica graph-state rank formula whose n = 3 partition structure drives these linear relations.")),
            Entry("two-three-party-reduction", "replica_three_two_and_three_party_reduction",
                "Explicit reduction of S_3^{(q)} to two- and three-party coarse-grained multi-entropies",
                ReductionFormula(),
                "For any q >= 3, normalized pure qubit stabilizer state psi, and colouring col : Fin N to Fin q, passing to a graph form Gamma writes 3 coarseMultiEntropy(pi, col, psi) = (log 2 / 2) upperRankSum(r, pi) on Pi_3(q) and coarseMultiEntropy(sigma, col, psi) = (log 2 / 2) upperRankSum(r, sigma) on Pi_2(q), where r(tau) = partitionRank(Gamma, col, tau). Applying coarse_upper_sum_reduction_and_triangular_inversion cancels the S(|X|, 2) + S(|Y|, 2) = 2^{|X|-1} + 2^{|Y|-1} - 2 three-block refinements of each two-block partition sigma = {X, Y} against coefficient 3 - 2^{|X|-1} - 2^{|Y|-1} and multiplies by 3^{2 - q} = (3^{q - 2})^{-1} to recover S(3, q, col, psi).",
                DescribeRole.Theorem),
            Paragraph(Text("For small party counts the reduction specializes directly. When q = 3, every two-block partition sigma in Pi_2(3) has block sizes 2 and 1, so 3 - 2^{2-1} - 2^{1-1} = 3 - 2 - 1 = 0 and 3^{2 - 3} * 3 S_3^{(3)}(bot) = S_3^{(3)}. When q = 4, the four singleton cuts with block sizes 3 and 1 carry coefficient 3 - 2^2 - 2^0 = -2, while the three balanced cuts with block sizes 2 and 2 carry coefficient 3 - 2^1 - 2^1 = -1, giving S_3^{(4)} = (1/9)[3 sum_{pi in Pi_3(4)} S_3^{(3)}(pi) - 2 sum_{|X|=1} S_3^{(2)}({X, Y}) - sum_{|X|=|Y|=2} S_3^{(2)}({X, Y})].")),
            Entry("vanishing-criterion", "coarse_linear_combination_and_vanishing_criterion",
                "Coarse-weight rank expansion and sufficient vanishing criterion for linear combinations",
                VanishingCriterionFormula(),
                "For q >= 2 and any real coefficient family c on partitions of Fin q, rewriting coarseMultiEntropy(rho, col, psi) = (log 2 / 2) * 3^{2 - |rho|} upperRankSum(r, rho) for |rho| >= 2 and exchanging summation over rho <= sigma equates sum_{|rho| >= 2} c(rho) coarseMultiEntropy(rho, col, psi) on every graph form Gamma of psi to (log 2 / 2) sum_{sigma in Pi_2(q) cup Pi_3(q)} coarseWeight(c, sigma) partitionRank(Gamma, col, sigma). Consequently, if coarseWeight(c, sigma) = 0 for all sigma in Pi_2(q) cup Pi_3(q), the linear combination vanishes identically across all qubit counts N, all normalized pure qubit stabilizer states, and all colourings into Fin q.",
                DescribeRole.Theorem),
            Paragraph(Text("For four parties (q = 4), Akella, Iizuka and Miyata, arXiv:2607.06050v1 Section II Eq. (5), define GM_3^{(4)} = S_3^{(4)} - (1/3) sum_{pi in Pi_3(4)} S_3^{(3)}(pi) + (1/3) sum_{|X|=1} S_3^{(2)}({X, Y}) - a I_3 with I_3 = sum_{|X|=1} S_3^{(2)}({X, Y}) - sum_{|X|=|Y|=2} S_3^{(2)}({X, Y}). Setting L = GM_3^{(4)} + (a - 1/9) I_3 assigns c(bot) = 1 (scaled by 3^{-2} = 1/9), c(pi) = -1/3 on Pi_3(4) (scaled by 3^{-1} = 1/3), c(sigma) = 2/9 on singleton cuts |X| = 1, and c(sigma) = 1/9 on balanced cuts |X| = |Y| = 2. Then coarseWeight(c, pi) = 1/9 - (1/3)(1/3) = 0 on Pi_3(4); each singleton cut refines from bot, three three-block partitions, and itself, giving 1/9 - 3(1/9) + 2/9 = 0; and each balanced cut refines from bot, two three-block partitions, and itself, giving 1/9 - 2(1/9) + 1/9 = 0. The vanishing criterion therefore yields GM_3^{(4)} = -(a - 1/9) I_3 for all normalized pure qubit stabilizer states, matching StabilizerMultiEntropyCollapse.result.")),
            Entry("coarse-determination", "coarse_two_three_data_determine_replica_three_multi_entropies",
                "Two- and three-party coarse data determine all replica-three multi-entropies",
                DeterminationFormula(),
                "Given normalized pure qubit stabilizer states psi on N qubits and psiPrime on NPrime qubits with colourings col : Fin N to Fin q and colPrime : Fin NPrime to Fin q (q >= 2), choose graph forms Gamma and GammaPrime. Because (log 2 / 2) * 3^{2 - k} != 0, equality of coarseMultiEntropy on Pi_2(q) and Pi_3(q) forces matching upper sums upperRankSum(r, sigma) = upperRankSum(rPrime, sigma) on Pi_2(q) and Pi_3(q). Triangular determination in coarse_upper_sum_reduction_and_triangular_inversion then equates upperRankSum(r, rho) = upperRankSum(rPrime, rho) for every partition rho, so coarseMultiEntropy(rho, col, psi) = coarseMultiEntropy(rho, colPrime, psiPrime) whenever |rho| >= 2, and evaluating at rho = bot equates S(3, q, col, psi) = S(3, q, colPrime, psiPrime).",
                DescribeRole.Theorem),
            Paragraph(Text("Scope and open boundary: all results here hold for normalized pure qubit stabilizer states at replica index n = 3 under the anchored replica convention; other replica indices n != 3, qudit stabilizer states, mixed states, and non-stabilizer states are outside scope, and no definition of genuine multi-entropy for q >= 5 is fixed. The vanishing criterion is proved in the sufficient direction only: because coarseWeight : c mapsto w is surjective by triangular back-substitution on twoOrThreePartitions(q), vanishing of L across all stabilizer states and colourings forces w_sigma = 0 for all sigma in Pi_2(q) cup Pi_3(q) if and only if the rank functionals (psi, col) mapsto partitionRank(Gamma, col, sigma) are linearly independent over normalized pure qubit stabilizer states, which remains an open question.")))));

    private static Formula ReductionFormula() => All(V("N"), Nat, All(V("q"), Nat,
        Imp(LeqRel(D(3), V("q")), All(Psi, State(V("N")),
            ImpP(StabilizerNorm(Psi, V("N")), All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                Equal(Call("S", D(3), V("q"), V("col"), Psi),
                    Multiply(Pow(D(3), Difference(D(2), Typed(V("q"), IntZ))),
                        Parenthesized(Seq(
                            SumOver(Mem(Pi, Call("partitionsOfCard", V("q"), D(3))),
                                Multiply(D(3), Call("coarseMultiEntropy", Pi, V("col"), Psi))),
                            Sp, Plus, Sp,
                            SumOver(Mem(SigmaLower, Call("partitionsOfCard", V("q"), D(2))),
                                Multiply(Difference(D(3), SumOver(Mem(V("B"), Call("parts", SigmaLower)),
                                        Pow(D(2), Difference(Call("card", V("B")), D(1))))),
                                    Call("coarseMultiEntropy", SigmaLower, V("col"), Psi)))))))))))));

    private static Formula VanishingCriterionFormula() => All(V("q"), Nat,
        Imp(LeqRel(D(2), V("q")), All(V("c"), Arrow(Call("PartyPartition", V("q")), Real),
            ConjAll(
                All(V("N"), Nat, All(Gamma, BinMatrix(V("N")), All(Psi, State(V("N")),
                    Imp(Call("IsGraphFormOf", Gamma, Psi), All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                        Equal(LinearComb(V("q"), V("c"), V("col"), Psi),
                            Multiply(Fraction(Call("log", D(2)), D(2)),
                                SumOver(Mem(SigmaLower, Call("twoOrThreePartitions", V("q"))),
                                    Multiply(Call("coarseWeight", V("c"), SigmaLower),
                                        Call("partitionRank", Gamma, V("col"), SigmaLower)))))))))),
                ImpP(
                    All(SigmaLower, Call("PartyPartition", V("q")),
                        Imp(Mem(SigmaLower, Call("twoOrThreePartitions", V("q"))),
                            Equal(Call("coarseWeight", V("c"), SigmaLower), D(0)))),
                    All(V("N"), Nat, All(Psi, State(V("N")),
                        ImpP(StabilizerNorm(Psi, V("N")), All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                            Equal(LinearComb(V("q"), V("c"), V("col"), Psi), D(0)))))))))));

    private static Formula DeterminationFormula() => All(V("N"), Nat, All(V("M"), Nat, All(V("q"), Nat,
        Imp(LeqRel(D(2), V("q")), All(Psi, State(V("N")), All(Phi, State(V("M")),
            ImpP(ConjAll(StabilizerNorm(Psi, V("N")), StabilizerNorm(Phi, V("M"))),
                All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(V("colB"), Arrow(Fin(V("M")), Fin(V("q"))),
                    ImpP(ConjAll(
                            All(SigmaLower, Call("PartyPartition", V("q")),
                                Imp(Mem(SigmaLower, Call("partitionsOfCard", V("q"), D(2))),
                                    Equal(Call("coarseMultiEntropy", SigmaLower, V("col"), Psi),
                                        Call("coarseMultiEntropy", SigmaLower, V("colB"), Phi)))),
                            All(Pi, Call("PartyPartition", V("q")),
                                Imp(Mem(Pi, Call("partitionsOfCard", V("q"), D(3))),
                                    Equal(Call("coarseMultiEntropy", Pi, V("col"), Psi),
                                        Call("coarseMultiEntropy", Pi, V("colB"), Phi))))),
                        ConjAll(
                            All(Rho, Call("PartyPartition", V("q")),
                                Imp(Mem(Rho, Call("nontrivialPartitions", V("q"))),
                                    Equal(Call("coarseMultiEntropy", Rho, V("col"), Psi),
                                        Call("coarseMultiEntropy", Rho, V("colB"), Phi)))),
                            Equal(Call("S", D(3), V("q"), V("col"), Psi),
                                Call("S", D(3), V("q"), V("colB"), Phi)))))))))))));

    private static Formula LinearComb(Formula q, Formula c, Formula col, Formula psi) =>
        SumOver(Mem(Rho, Call("nontrivialPartitions", q)),
            Multiply(Apply(c, Rho), Call("coarseMultiEntropy", Rho, col, psi)));
    private static Formula StabilizerNorm(Formula psi, Formula n) => ConjAll(
        Call("StabilizedBy", V("pauliSet"), psi),
        Equal(SumOver(Typed(V("x"), Arrow(Fin(n), Fin(D(2)))), Pow(new Formula.Norm(Apply(psi, V("x"))), D(2))), D(1)));
    private static Formula BinMatrix(Formula n) => Call("Matrix", Fin(n), Fin(n), Call("ZMod", D(2)));
    private static Formula State(Formula n) => Arrow(Arrow(Fin(n), Fin(D(2))), Seq(Mathbb, Grp(V("C"))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula statement,
        string explanation, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula IntZ => Seq(Mathbb, Grp(V("Z")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula name, Formula type) => Parenthesized(Seq(name, Sp, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeqRel(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, Parenthesized(b));
    private static Formula ImpP(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Rightarrow, Sp, Parenthesized(b));
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
