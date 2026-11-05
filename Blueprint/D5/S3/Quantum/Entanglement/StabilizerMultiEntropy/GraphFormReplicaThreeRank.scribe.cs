using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class GraphFormReplicaThreeRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/akella2026genuine");
    private static readonly LibraryNoteRef GraphSource =
        LibraryNoteRef.Create("D5/L/QuantumStates/vandennest2004graphical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every normalized pure qubit stabilizer state admits a graph form on which opposite nonzero ternary replica characters biject onto two- and three-block party partitions, expressing the replica-three multi-entropy and its coarse-grainings as sums of masked F2 adjacency ranks.",
        H("Replica-three stabilizer multi-entropy via graph forms and coarse party partitions"),
        Blocks(
            Paragraph(Text("Following the replica convention of Gadde, Krishna and Sharma, Phys. Rev. D 106, 126001, in the anchored form of Akella, Iizuka and Miyata, arXiv:2607.06050v1 Appendix A, a q-party pure N-qubit state psi with colouring col : Fin N to Fin q (allowing empty parties) is contracted over replicas r in (Z/3Z)^{q-1}, with the last party q - 1 acting by the identity. By Van den Nest, Dehaene and De Moor, Phys. Rev. A 69, 022316, and Schlingemann, Quantum Inf. Comput. 2, 307-323, every normalized pure qubit stabilizer state is local-unitary equivalent up to a unit phase to a graph state |Gamma>. Akella and Gadde, arXiv:2610.27080v1 Section II Eqs. (7)-(9) and Appendix A, give an odd-replica rank formula for graph states whose n = 3 specialization groups nonzero F4 labels by equality partition; retaining the factor n^{-(q-2)} yields the coarse-partition rank sum proved below.")),
            Entry("graph-state", "graphState", "Normalized N-qubit graph state",
                All(V("N"), Nat, All(Gamma, BinMatrix,
                    Equal(Call("graphState", Gamma),
                        Multiply(Typed(Pow(D(2), Seq(Minus, Fraction(Typed(V("N"), Real), D(2)))), Complex),
                            Call("graphAmp", Gamma))))),
                "Scales the unnormalized binary quadratic phase vector graphAmp(Gamma) by 2^{-N/2} so that |Gamma> has unit Hilbert norm.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(GraphSource)),
            Entry("is-graph-form-of", "IsGraphFormOf", "Graph form of a pure qubit state",
                All(V("N"), Nat, All(Gamma, BinMatrix, All(Psi, State,
                    Seq(Call("IsGraphFormOf", Gamma, Psi), Sp, Leftrightarrow, Sp,
                        Parenthesized(ConjAll(
                            Call("IsSymm", Gamma),
                            All(V("u"), Fin(V("N")), Equal(Apply(Gamma, V("u"), V("u")), D(0))),
                            Ex(V("U"), LocalUnitaries, Ex(LambdaLower, Complex,
                                ConjAll(
                                    All(V("u"), Fin(V("N")),
                                        Mem(Apply(V("U"), V("u")), Call("unitaryGroup", Fin(D(2)), Complex))),
                                    Equal(new Formula.Norm(LambdaLower), D(1)),
                                    Equal(Psi, Multiply(LambdaLower,
                                        Call("mulVec", Call("tensorOp", V("U")), Call("graphState", Gamma))))))))))))),
                "Asserts that Gamma is symmetric over ZMod 2 with zero diagonal and that psi equals lambda * (U_0 x ... x U_{N-1}) |Gamma> for single-qubit unitaries U(u) and a scalar lambda with ||lambda|| = 1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(GraphSource)),
            Entry("party-delta", "partyDelta", "Anchored party translation vector",
                All(V("q"), Nat, All(V("c"), Fin(V("q")), All(V("i"), Fin(Difference(V("q"), D(1))),
                    Equal(Call("partyDelta", V("c"), V("i")),
                        Call("ite", Equal(Typed(V("i"), Nat), Typed(V("c"), Nat)), D(1), D(0)))))),
                "Assigns the c-th standard basis vector of (Z/3Z)^{q-1} to party c < q - 1 and the zero vector to the last party q - 1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Entry("char-eval", "charEval", "Party evaluation of a ternary character",
                All(V("q"), Nat, All(V("t"), RepVec, All(V("c"), Fin(V("q")),
                    Equal(Call("charEval", V("t"), V("c")),
                        SumOver(Typed(V("i"), Fin(Difference(V("q"), D(1)))),
                            Multiply(Apply(V("t"), V("i")), Call("partyDelta", V("c"), V("i")))))))),
                "Evaluates f_t(c) = t . delta_c in Z/3Z, taking value t_c for c < q - 1 and 0 on the last party q - 1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Entry("char-partition", "charPartition", "Fibre partition of a ternary character",
                All(V("q"), Nat, All(V("t"), RepVec,
                    Equal(Call("charPartition", V("t")), Call("ofSetoid", Call("ker", Call("charEval", V("t"))))))),
                "Partitions Fin q into the nonempty fibres of charEval(t).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Entry("coarse-multi-entropy", "coarseMultiEntropy", "Coarse-grained replica-three multi-entropy",
                All(V("N"), Nat, All(V("q"), Nat, All(Pi, Call("PartyPartition", V("q")),
                    All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(Psi, State,
                        Equal(Call("coarseMultiEntropy", Pi, V("col"), Psi),
                            Call("S", D(3), Call("card", Call("parts", Pi)),
                                Call("coarseCol", Pi, Call("symm", Call("equivFin", Call("parts", Pi))), V("col")), Psi))))))),
                "Evaluates S_3^{(|pi|)} on psi under the coarse-grained colouring induced by the canonical block enumeration of pi.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Entry("graph-form-replica-rank", "graph_form_existence_and_replica_rank_formula",
                "Unit replica-one contraction, graph-form existence, and replica-three rank contraction",
                GraphFormRankFormula(),
                "Shows that Z(1, q, col, psi) = 1 whenever sum_x ||psi(x)||^2 = 1; extracts a symmetric zero-diagonal graph form Gamma for every normalized pure qubit stabilizer state by factoring the reciprocal norm 2^{-N/2} out of the stabilizer normal-form scalar; and proves for every graph form Gamma of psi and every opposite-pair representative set P in (Z/3Z)^{q-1} that psi has unit norm and Z(3, q, col, psi) is a positive real number equal to 2^{-sum_{t in P} rank C(Gamma, delta(col), t)}.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("replica-three-coarse-sum", "replica_three_coarse_partition_sum",
                "Bijection of opposite ternary characters onto coarse partitions and the partition-rank sum for S_3^{(q)}",
                CoarsePartitionSumFormula(),
                "Because negation is a bijection of Z/3Z, charEval(-t) = -charEval(t) has the same fibres as charEval(t), giving charPartition(-t) = charPartition(t). For q >= 2 and nonzero t, charEval(t) vanishes at q - 1 and takes at least one nonzero value in Z/3Z, so charPartition(t) has two or three blocks. Identifying Fin q with Option(Fin(q - 1)) reduces injectivity on P to TernaryPartitionOrbit, while assigning 0 to the block of q - 1 and injective values in {1, 2} to the remaining one or two blocks proves surjectivity onto twoOrThreePartitions(q). Counting both sides yields (3^{q-1} - 1)/2 = S(q, 2) + S(q, 3), and C(Gamma, delta(col), t) coincides entrywise with maskedAdj(Gamma, col, charPartition(t)), transforming the replica rank sum into (log 2 / (2 * 3^{q-2})) sum_{pi in Pi_2(q) cup Pi_3(q)} partitionRank(Gamma, col, pi).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("party-symmetry-bipartite", "party_symmetry_coarse_graining_and_bipartite_entropy",
                "Party-permutation invariance, coarse-graining upper sum, and bipartite off-diagonal rank formula",
                PartySymmetryFormula(),
                "Pulling partitions back along a surjective party map m : Fin q to Fin k bijects twoOrThreePartitions(k) onto the two- and three-block partitions sigma >= ker(m) while preserving maskedAdj and partitionRank. When m is a permutation tau of Fin q, ker(tau) is the discrete partition bot, proving S(3, q, tau o col, psi) = S(3, q, col, psi). When m comes from any block listing B : Fin k to pi.parts with |pi| >= 2, ker(m) = pi, proving block-order independence S(3, k, coarseCol(pi, B, col), psi) = coarseMultiEntropy(pi, col, psi), recovery coarseMultiEntropy(bot, col, psi) = S(3, q, col, psi), and the upper-sum formula (log 2 / (2 * 3^{|pi|-2})) sum_{sigma >= pi} partitionRank(Gamma, col, sigma). For a two-block partition sigma = {X, Y}, sigma is maximal in twoOrThreePartitions(q) and bipartite_masked_antidiagonal_rank gives partitionRank(Gamma, col, sigma) = 2 rank(offDiagBlock(Gamma, col, X, Y)), so coarseMultiEntropy(sigma, col, psi) = log 2 * rank(Gamma_{X,Y}).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Paragraph(Text("For a two-block partition sigma = {X, Y}, the identity S_3^{(2)}(sigma) = log 2 * rank_{F2}(Gamma_{X,Y}) matches the bipartite Renyi entanglement entropy of a graph state established by Hein, Eisert and Briegel, Phys. Rev. A 69, 062311. As an explicit three-party illustration, for the three-qubit chain graph state with adjacency edges (0, 1) and (1, 2) and one qubit per party (q = 3, col = id), the three two-block partitions {01, 2}, {02, 1}, {12, 0} and the single three-block partition {0, 1, 2} each produce a masked 3 x 3 binary matrix of rank 2; the coarse-partition sum therefore gives S_3^{(3)} = (log 2 / (2 * 3^1)) * (2 + 2 + 2 + 2) = (4/3) log 2, matching the chain formula (1 + 1/n) log 2 at n = 3 in Czech, Feng, Wu and Xie, arXiv:2606.06582v2 Appendix B Eq. (B.9).")))));

    private static Formula GraphFormRankFormula() => ConjAll(
        All(V("N"), Nat, All(V("q"), Nat, All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(Psi, State,
            Imp(NormOne(Psi), Equal(Call("Z", D(1), V("q"), V("col"), Psi), D(1))))))),
        All(V("N"), Nat, All(Psi, State,
            ImpP(ConjAll(Call("StabilizedBy", V("pauliSet"), Psi), NormOne(Psi)),
                Ex(Gamma, BinMatrix, Call("IsGraphFormOf", Gamma, Psi))))),
        All(V("N"), Nat, All(V("q"), Nat, All(Gamma, BinMatrix, All(Psi, State,
            Imp(Call("IsGraphFormOf", Gamma, Psi),
                All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(V("P"), RepSetType,
                    ImpP(OppPairRep(V("P")),
                        ConjAll(
                            NormOne(Psi),
                            Seq(D(0), Sp, Lt, Sp, Call("Re", Call("Z", D(3), V("q"), V("col"), Psi))),
                            Equal(Call("Im", Call("Z", D(3), V("q"), V("col"), Psi)), D(0)),
                            Equal(Call("Z", D(3), V("q"), V("col"), Psi),
                                Pow(Parenthesized(Pow(D(2), SumOver(Mem(V("t"), V("P")),
                                    Call("rank", Call("C", Gamma, Call("delta", V("col")), V("t")))))),
                                    Seq(Minus, D(1))))))))))))));

    private static Formula CoarsePartitionSumFormula() => ConjAll(
        All(V("q"), Nat, All(V("t"), RepVec,
            Equal(Call("charPartition", Seq(Minus, V("t"))), Call("charPartition", V("t"))))),
        All(V("q"), Nat, Imp(LeqRel(D(2), V("q")), All(V("P"), RepSetType,
            ImpP(OppPairRep(V("P")),
                ConjAll(
                    Call("BijOn", V("charPartition"), V("P"), Call("twoOrThreePartitions", V("q"))),
                    Equal(Typed(Call("card", V("P")), Real),
                        Fraction(Difference(Pow(Typed(D(3), Real), Difference(V("q"), D(1))), D(1)), D(2))),
                    Equal(Fraction(Difference(Pow(Typed(D(3), Real), Difference(V("q"), D(1))), D(1)), D(2)),
                        Seq(Typed(Call("stirlingSecond", V("q"), D(2)), Real), Sp, Plus, Sp, Typed(Call("stirlingSecond", V("q"), D(3)), Real)))))))),
        All(V("N"), Nat, All(V("q"), Nat, Imp(LeqRel(D(2), V("q")),
            All(Gamma, BinMatrix, All(Psi, State, Imp(Call("IsGraphFormOf", Gamma, Psi),
                All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                    Equal(Call("S", D(3), V("q"), V("col"), Psi),
                        Multiply(Fraction(Call("log", D(2)), Multiply(D(2), Pow(D(3), Difference(V("q"), D(2))))),
                            SumOver(Mem(Pi, Call("twoOrThreePartitions", V("q"))),
                                Call("partitionRank", Gamma, V("col"), Pi))))))))))));

    private static Formula PartySymmetryFormula() => ConjAll(
        All(V("N"), Nat, All(V("q"), Nat, Imp(LeqRel(D(2), V("q")),
            All(Psi, State, ImpP(ConjAll(Call("StabilizedBy", V("pauliSet"), Psi), NormOne(Psi)),
                All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(Tau, Call("Perm", Fin(V("q"))),
                    Equal(Call("S", D(3), V("q"), Seq(Tau, Sp, Circ, Sp, V("col")), Psi),
                        Call("S", D(3), V("q"), V("col"), Psi))))))))),
        All(V("N"), Nat, All(V("q"), Nat, All(V("k"), Nat,
            All(Gamma, BinMatrix, All(Psi, State, Imp(Call("IsGraphFormOf", Gamma, Psi),
                All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(Pi, Call("PartyPartition", V("q")),
                    Imp(LeqRel(D(2), Call("card", Call("parts", Pi))),
                        All(V("B"), Call("Equiv", Fin(V("k")), Call("parts", Pi)),
                            ConjAll(
                                Equal(Call("S", D(3), V("k"), Call("coarseCol", Pi, V("B"), V("col")), Psi),
                                    Call("coarseMultiEntropy", Pi, V("col"), Psi)),
                                Equal(Call("coarseMultiEntropy", Pi, V("col"), Psi),
                                    Multiply(Fraction(Call("log", D(2)), Multiply(D(2), Pow(D(3), Difference(Call("card", Call("parts", Pi)), D(2))))),
                                        SumOver(Conj(Mem(SigmaLower, Call("twoOrThreePartitions", V("q"))), LeqRel(Pi, SigmaLower)),
                                            Call("partitionRank", Gamma, V("col"), SigmaLower))))))))))))))),
        All(V("N"), Nat, All(V("q"), Nat, Imp(LeqRel(D(2), V("q")),
            All(Psi, State, ImpP(ConjAll(Call("StabilizedBy", V("pauliSet"), Psi), NormOne(Psi)),
                All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                    Equal(Call("coarseMultiEntropy", Typed(Call("bot"), Call("PartyPartition", V("q"))), V("col"), Psi),
                        Call("S", D(3), V("q"), V("col"), Psi)))))))),
        All(V("N"), Nat, All(V("q"), Nat, All(Gamma, BinMatrix, All(Psi, State,
            Imp(Call("IsGraphFormOf", Gamma, Psi),
                All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(SigmaLower, Call("PartyPartition", V("q")),
                    Imp(Mem(SigmaLower, Call("partitionsOfCard", V("q"), D(2))),
                        All(V("X"), Call("Finset", Fin(V("q"))), All(V("Y"), Call("Finset", Fin(V("q"))),
                            ImpP(ConjAll(Equal(Call("parts", SigmaLower), Call("pair", V("X"), V("Y"))), Seq(V("X"), Sp, Neq, Sp, V("Y"))),
                                Equal(Call("coarseMultiEntropy", SigmaLower, V("col"), Psi),
                                    Multiply(Call("log", D(2)), Call("rank", Call("offDiagBlock", Gamma, V("col"), V("X"), V("Y")))))))))))))))));

    private static Formula OppPairRep(Formula p) => ConjAll(
        Seq(Neg, Parenthesized(Mem(D(0), p))),
        All(V("t"), RepVec, Imp(Seq(V("t"), Sp, Neq, Sp, D(0)),
            Seq(Mem(V("t"), p), Sp, Leftrightarrow, Sp,
                Seq(Neg, Parenthesized(Mem(Seq(Minus, V("t")), p)))))));
    private static Formula NormOne(Formula psi) => Equal(SumOver(Typed(V("x"), Arrow(Fin(V("N")), Fin(D(2)))),
        Pow(new Formula.Norm(Apply(psi, V("x"))), D(2))), D(1));
    private static Formula BinMatrix => Call("Matrix", Fin(V("N")), Fin(V("N")), Call("ZMod", D(2)));
    private static Formula LocalUnitaries => Arrow(Fin(V("N")), Call("Matrix", Fin(D(2)), Fin(D(2)), Complex));
    private static Formula State => Arrow(Arrow(Fin(V("N")), Fin(D(2))), Complex);
    private static Formula RepVec => Arrow(Fin(Difference(V("q"), D(1))), Call("ZMod", D(3)));
    private static Formula RepSetType => Call("Finset", RepVec);

    private static DocumentBlock Entry(string id, string declaration, string title, Formula statement,
        string explanation, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), provenance,
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
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
