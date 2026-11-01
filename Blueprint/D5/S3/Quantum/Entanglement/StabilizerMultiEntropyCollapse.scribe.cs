using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class StabilizerMultiEntropyCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/akella2026genuine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a normalized pure qubit stabilizer state, ternary replica contractions are positive real numbers. Their four-party genuine multi-entropy is determined by the tripartite information.",
        H("The ternary replica collapse for four-party stabilizer states"),
        Blocks(
            Paragraph(Text("Akella and Gadde, Renyi multi-entropy of graph states and the n to 1 limit, arXiv:2610.27080v1, Section II Eqs. (7)-(9) and Appendix A, give an odd-replica rank formula that also implies this n=3 four-party relation. For the three nonzero F4 labels, diagonal rescaling makes the rank depend only on their equality partition. The entropy normalization here retains n^{-(q-2)}, which their Eq. (2) explicitly omits. The partition counts then give the coefficient 1/9. This is a structural formal proof and reusable library growth for an existing conclusion, with no new unique-solve or global-priority claim. The resolution slug below preserves the existing project resolution; the open counting question in arXiv:2607.06050v2 Section 6 is a source-text statement, not a current no-other-proof certificate.")),
            Entry("shift", "shift", "Shifting a replica coordinate", ShiftFormula(),
                "Replica labels are functions Fin(q - 1) to Z/nZ. The shift adds one at the coordinate whose natural index equals the colour c. Colour q - 1 has no such coordinate and acts as the identity. Natural differences such as q - 1 and q - 2 in these formulas use truncated subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("partition-function", "Z", "Contracting the replicas", PartitionFunction(),
                "A configuration x assigns a binary N-qubit string to each replica label r. The conjugated amplitude is evaluated at x(r); the other amplitude takes qubit u from the replica shifted by its colour col(u). Summing the product gives the computational-basis contraction of Appendix A.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("delta", "delta", "Ternary replica translation vector", DeltaFormula(),
                "For a colouring col : Fin N to Fin q, delta(col, u) is the standard basis vector in (Z/3Z)^{q-1} at coordinate col(u) when col(u) < q - 1, and zero when col(u) = q - 1, so shift(3, q, col(u), r) = r + delta(col, u).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Entry("z-smul", "Z_smul", "Scalar homogeneity of the replica contraction", ZSmulFormula(),
                "Scaling a pure state amplitude by c in C multiplies each of the n^{q-1} replica factors by star(c) * c, scaling Z(n, q, col, c * psi) by (star(c) * c)^{n^{q-1}}.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("z-one", "Z_one", "Replica contraction at index one", ZOneFormula(),
                "At replica index n = 1 the replica group (Z/1Z)^{q-1} has a unique element on which every shift acts trivially, reducing Z(1, q, col, psi) to the cast of the squared Hilbert norm sum_x ||psi(x)||^2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("z-local-scalar", "Z_local_scalar", "Invariance under product unitaries and scalars", ZLocalScalarFormula(),
                "Applying a tensor product tensorOp(U) of single-qubit unitaries U(u) commutes with replica coordinate permutations on each qubit wire and cancels against its adjoint in the replica inner product, leaving Z(n, q, col, c * (tensorOp(U) * psi)) equal to Z(n, q, col, c * psi).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("graph-scalar-norm", "graph_scalar_norm", "Squared modulus of a normalized local-unitary graph amplitude", GraphScalarNormFormula(),
                "Because the unnormalized graph amplitude graphAmp(A) has 2^N unit-modulus entries and product unitaries preserve the squared norm via Z_local_scalar and Z_one at (n, q) = (1, 1), unit Hilbert norm of c * (tensorOp(U) * graphAmp(A)) forces star(c) * c = (2^N)^{-1}.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("graph-count", "graph_count", "Ternary graph contraction as a reciprocal power of two", GraphCountFormula(),
                "For any symmetric binary matrix A, colouring col : Fin N to Fin q, and opposite-pair representative set P of nonzero vectors in (Z/3Z)^{q-1}, the ternary quadratic normal form splits the unnormalized graph contraction into one zero-mode factor 2^N and |P| bilinear blocks of size 2^(2N - rank C_t); multiplying by ((2^N)^{-1})^{3^{q-1}} yields 2^{-sum_{t in P} rank C(A, delta(col), t)}.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("representatives-exist", "representatives_exist", "Existence of opposite-mode representatives", RepresentativesExistFormula(),
                "Ordering (Z/3Z)^d by an equivalence to Fin(3^d) and selecting those vectors strictly preceding their negation produces a finite set P avoiding 0 and containing, for every nonzero t, either t or -t but not both.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("entropy", "S", "The normalized multi-entropy", Entropy(),
                "The normalization divides Z(n,q,col,psi) by the indicated power of Z(1,q,col,psi). The logarithm is applied to the real part of the quotient, with the prefactors specified in Appendix A. The casts of n to R appear explicitly.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("entropy-formula", "entropy_formula", "Replica-three multi-entropy from a reciprocal-power contraction", EntropyFormula(),
                "When psi has unit squared norm so Z(1, q, col, psi) = 1 and Z(3, q, col, psi) equals the reciprocal of 2^{sum_{t in P} rank C(A, delta(col), t)}, substituting into S(3, q, col, psi) evaluates the real logarithm to -(sum_{t in P} rank C_t) log 2 and cancels 1/(1 - 3) = -1/2 to give (log 2 / (2 * 3^{q-2})) sum_{t in P} rank C(A, delta(col), t).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Entry("tripartite-information", "I3", "Four cuts minus three cuts", TripartiteInformation(),
                "Label A, B, C, D by 0, 1, 2, 3. Each displayed tuple is a function from Fin 4 to the stated colour set, composed with party. In order, the four positive terms are ABC:D, ABD:C, ACD:B and BCD:A; the three subtracted terms are AB:CD, AC:BD and AD:BC. This is the Renyi tripartite information I_{3,n} in Eq. (1) of the paper.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("genuine-entropy", "GM4", "The genuine four-party combination", GenuineEntropy(),
                "The six three-colour tuples merge AB, AC, AD, BC, BD and CD, respectively. Their entropies have coefficient -1/3, while the four singleton cuts have coefficient 1/3. The remaining term is -a times the tripartite information, for an arbitrary real parameter a, as in Section 2 of the paper.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("collapse-proposition", "claim", "Positivity and the n = 3 collapse", CollapseClaim(),
                "The proposition quantifies over every qubit count, every assignment to four labelled parties and every amplitude. Its two assumptions are Pauli stabilization and unit squared norm. The first conclusion includes every colour count and colouring and asserts both strict positivity of the real part and a zero imaginary part. The second conclusion is Eq. (3) for every real a, with I3 interpreted as I_{3,3}. Empty parties are allowed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("collapse", "result", "The stabilizer collapse", V("claim"),
                "A stabilizer state is a scalar multiple of a local-unitary image of the unnormalized graphAmp Gamma, which has 2^N entries of modulus one, hence squared Hilbert norm 2^N. For arbitrary N including 0, odd n >= 3, q >= 2, colouring col : Fin N to Fin q, binary matrix Gamma and local unitaries U, if psi = c * (tensorOp U * graphAmp Gamma) has unit squared Hilbert norm, tensor unitarity preserves Hilbert norm, so normalization fixes star c * c = (2^N)^{-1}. Local-unitary invariance and homogeneity reduce Z(n,q,col,psi) to (((2^N)^{-1})^{n^{q-1}}) Z(n,q,col,graphAmp Gamma). At n = 3, the graph replica translation form decomposes into bilinear blocks indexed by opposite nonzero Fourier modes. Each block contributes the inverse power of two determined by its rank, giving positive real contractions whose ranks depend only on the equality partition of the party colours. TernaryPartitionCounting supplies the generic merger transport and weighted counting identity consumed here, while TernaryPartitionOrbit classifies nonzero anchored modes modulo sign by their equality partitions. With four labels, the finite partition coefficients 1, -1, 2 and 1 for the full term, six pair mergers, four singleton cuts and three balanced cuts cancel at every induced two- or three-block partition, yielding GM4(3, a, party, psi) = -(a - 1/9) I3(3, party, psi) without settling other replica indices.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("akella-2026-stabilizer-multi-entropy-n3-collapse"), ResolutionKind.Proved)))));

    private static Formula ShiftFormula() => All(V("n"), Nat, All(V("q"), Nat,
        All(V("c"), Fin(V("q")), All(V("r"), Replicas(V("n"), V("q")),
            Equal(Call("shift", V("n"), V("q"), V("c"), V("r")),
                Seq(Typed(V("i"), Fin(Difference(V("q"), D(1)))), Sp, Mapsto, Sp,
                    Call("ite", Equal(Typed(V("i"), Nat), Typed(V("c"), Nat)),
                        Seq(Call("r", V("i")), Sp, Plus, Sp, D(1)), Call("r", V("i")))))))));

    private static Formula PartitionFunction() => ReplicaArguments(Equal(
        Call("Z", V("n"), V("q"), V("col"), Psi),
        SumOver(Typed(V("x"), Arrow(Replicas(V("n"), V("q")), Bits)),
            ProdOver(Typed(V("r"), Replicas(V("n"), V("q"))),
                Multiply(Call("star", Apply(Psi, Call("x", V("r")))),
                    Apply(Psi, Parenthesized(Seq(Typed(V("u"), Fin(V("N"))), Sp, Mapsto, Sp,
                        Call("x", Call("shift", V("n"), V("q"), Call("col", V("u")), V("r")), V("u"))))))))));

    private static Formula DeltaFormula() => All(V("N"), Nat, All(V("q"), Nat,
        All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(V("u"), Fin(V("N")),
            Equal(Call("delta", V("col"), V("u")),
                Seq(Typed(V("i"), Fin(Difference(V("q"), D(1)))), Sp, Mapsto, Sp,
                    Call("ite", Equal(Typed(V("i"), Nat), Typed(Call("col", V("u")), Nat)), D(1), D(0))))))));

    private static Formula ZSmulFormula() => All(V("N"), Nat, All(V("n"), Nat, All(V("q"), Nat,
        Instance(Call("NeZero", V("n")), All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
            All(Psi, State, All(V("c"), Complex,
                Equal(Call("Z", V("n"), V("q"), V("col"), Multiply(V("c"), Psi)),
                    Multiply(Pow(Parenthesized(Multiply(Call("star", V("c")), V("c"))),
                            Pow(V("n"), Difference(V("q"), D(1)))),
                        Call("Z", V("n"), V("q"), V("col"), Psi))))))))));

    private static Formula ZOneFormula() => All(V("N"), Nat, All(V("q"), Nat,
        All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(Psi, State,
            Equal(Call("Z", D(1), V("q"), V("col"), Psi),
                Typed(NormSqSum(Psi), Complex))))));

    private static Formula ZLocalScalarFormula() => All(V("N"), Nat, All(V("n"), Nat, All(V("q"), Nat,
        Instance(Call("NeZero", V("n")), All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
            All(Psi, State, All(V("U"), LocalUnitaries,
                ImpP(UnitariesMem(V("U")), All(V("c"), Complex,
                    Equal(Call("Z", V("n"), V("q"), V("col"), Multiply(V("c"), Call("mulVec", Call("tensorOp", V("U")), Psi))),
                        Call("Z", V("n"), V("q"), V("col"), Multiply(V("c"), Psi))))))))))));

    private static Formula GraphScalarNormFormula() => All(V("N"), Nat, All(V("A"), BinMatrix,
        All(V("U"), LocalUnitaries, ImpP(UnitariesMem(V("U")), All(V("c"), Complex,
            ImpP(Equal(NormSqSum(Parenthesized(Multiply(V("c"), Call("mulVec", Call("tensorOp", V("U")), Call("graphAmp", V("A")))))), D(1)),
                Equal(Multiply(Call("star", V("c")), V("c")), RecipPowTwo(V("N")))))))));

    private static Formula GraphCountFormula() => All(V("N"), Nat, All(V("q"), Nat, All(V("A"), BinMatrix,
        ImpP(SymmEntries(V("A")), All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
            All(V("P"), Call("Finset", Replicas(D(3), V("q"))),
                ImpP(OppPairRep(V("P"), Difference(V("q"), D(1))),
                    Equal(Multiply(Pow(Parenthesized(RecipPowTwo(V("N"))), Pow(D(3), Difference(V("q"), D(1)))),
                            Call("Z", D(3), V("q"), V("col"), Call("graphAmp", V("A")))),
                        RecipPowTwo(RankSumOverP(V("A"), V("col"), V("P")))))))))));

    private static Formula RepresentativesExistFormula() => All(V("d"), Nat,
        Seq(Exists, Sp, Typed(V("P"), Call("Finset", Arrow(Fin(V("d")), Call("ZMod", D(3))))), Comma, Sp,
            OppPairRep(V("P"), V("d"))));

    private static Formula Entropy() => ReplicaArguments(Equal(Call("S", V("n"), V("q"), V("col"), Psi),
        Multiply(Multiply(Fraction(D(1), Parenthesized(Seq(D(1), Sp, Minus, Sp, Typed(V("n"), Real)))),
                Fraction(D(1), Pow(Typed(V("n"), Real), Difference(V("q"), D(2))))),
            Call("log", Call("Re", Fraction(Call("Z", V("n"), V("q"), V("col"), Psi),
                Pow(Call("Z", D(1), V("q"), V("col"), Psi), Pow(V("n"), Difference(V("q"), D(1))))))))));

    private static Formula EntropyFormula() => All(V("N"), Nat, All(Psi, State,
        ImpP(Equal(NormSqSum(Psi), D(1)), All(V("q"), Nat, All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
            All(V("A"), BinMatrix, All(V("P"), Call("Finset", Replicas(D(3), V("q"))),
                ImpP(Equal(Call("Z", D(3), V("q"), V("col"), Psi), RecipPowTwo(RankSumOverP(V("A"), V("col"), V("P")))),
                    Equal(Call("S", D(3), V("q"), V("col"), Psi),
                        Multiply(Fraction(Call("log", D(2)), Multiply(D(2), Pow(D(3), Difference(V("q"), D(2))))),
                            RankSumOverP(V("A"), V("col"), V("P"))))))))))));

    private static Formula TripartiteInformation() => PartyArguments(Equal(
        Call("I3", V("n"), V("party"), Psi),
        Seq(SingletonCuts(), Sp, Minus, Sp, Parenthesized(
            Add(Cut(D(2), 0, 0, 1, 1), Cut(D(2), 0, 1, 0, 1), Cut(D(2), 0, 1, 1, 0))))));

    private static Formula GenuineEntropy() => All(V("n"), Nat, Instance(Call("NeZero", V("n")),
        All(V("a"), Real, All(V("N"), Nat, All(V("party"), Arrow(Fin(V("N")), Fin(D(4))), All(Psi, State,
            Equal(Call("GM4", V("n"), V("a"), V("party"), Psi),
                Seq(Call("S", V("n"), D(4), V("party"), Psi), Sp, Minus, Sp,
                    Multiply(Fraction(D(1), D(3)), Parenthesized(Add(
                        Cut(D(3), 0, 0, 1, 2), Cut(D(3), 0, 1, 0, 2), Cut(D(3), 0, 1, 2, 0),
                        Cut(D(3), 1, 0, 0, 2), Cut(D(3), 1, 0, 2, 0), Cut(D(3), 1, 2, 0, 0)))), Sp, Plus, Sp,
                    Multiply(Fraction(D(1), D(3)), Parenthesized(SingletonCuts())), Sp, Minus, Sp,
                    Multiply(V("a"), Call("I3", V("n"), V("party"), Psi))))))))));

    private static Formula CollapseClaim() => Seq(V("claim"), Sp, Leftrightarrow, Sp, Parenthesized(
        All(V("N"), Nat, All(V("party"), Arrow(Fin(V("N")), Fin(D(4))), All(Psi, State,
            Imp(Call("StabilizedBy", V("pauliSet"), Psi),
                ImpP(Equal(NormSqSum(Psi), D(1)),
                    Conj(Parenthesized(All(V("q"), Nat, All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                            Conj(Seq(D(0), Sp, Lt, Sp, Call("Re", Call("Z", D(3), V("q"), V("col"), Psi))),
                                Equal(Call("Im", Call("Z", D(3), V("q"), V("col"), Psi)), D(0)))))),
                        All(V("a"), Real, Equal(Call("GM4", D(3), V("a"), V("party"), Psi),
                            Multiply(Seq(Minus, Parenthesized(Seq(V("a"), Sp, Minus, Sp, Fraction(D(1), D(9))))),
                                Call("I3", D(3), V("party"), Psi))))))))))));

    private static Formula NormSqSum(Formula psi) => SumOver(Typed(V("x"), Bits),
        Pow(new Formula.Norm(Apply(psi, V("x"))), D(2)));
    private static Formula BinMatrix => Call("Matrix", Fin(V("N")), Fin(V("N")), Call("ZMod", D(2)));
    private static Formula LocalUnitaries => Arrow(Fin(V("N")), Call("Matrix", Fin(D(2)), Fin(D(2)), Complex));
    private static Formula UnitariesMem(Formula u) => All(V("u"), Fin(V("N")),
        Seq(Apply(u, V("u")), Sp, InMacro, Sp, Call("unitaryGroup", Fin(D(2)), Complex)));
    private static Formula SymmEntries(Formula a) => All(V("u"), Fin(V("N")), All(V("v"), Fin(V("N")),
        Equal(Apply(a, V("u"), V("v")), Apply(a, V("v"), V("u")))));
    private static Formula OppPairRep(Formula p, Formula d) => Conj(
        Seq(Neg, Parenthesized(Seq(D(0), Sp, InMacro, Sp, p))),
        All(V("t"), Arrow(Fin(d), Call("ZMod", D(3))),
            ImpP(Seq(V("t"), Sp, Neq, Sp, D(0)),
                Seq(Seq(V("t"), Sp, InMacro, Sp, p), Sp, Leftrightarrow, Sp,
                    Seq(Neg, Parenthesized(Seq(Seq(Minus, V("t")), Sp, InMacro, Sp, p)))))));
    private static Formula RecipPowTwo(Formula exp) => Pow(Parenthesized(Pow(D(2), exp)), Seq(Minus, D(1)));
    private static Formula RankSumOverP(Formula a, Formula col, Formula p) =>
        SumOver(Seq(V("t"), Sp, InMacro, Sp, p), Call("rank", Call("C", a, Call("delta", col), V("t"))));
    private static Formula SingletonCuts() => Add(Cut(D(2), 0, 0, 0, 1), Cut(D(2), 0, 0, 1, 0),
        Cut(D(2), 0, 1, 0, 0), Cut(D(2), 1, 0, 0, 0));
    private static Formula Cut(Formula q, params byte[] colours) => Call("S", V("n"), q,
        Parenthesized(Seq(Typed(Tuple(colours), Arrow(Fin(D(4)), Fin(q))), Sp, Circ, Sp, V("party"))), Psi);
    private static Formula Tuple(byte[] entries) => Seq(OpenBracket,
        Seq([.. entries.SelectMany((x, i) => i == 0 ? new Formula[] { D(x) } : new Formula[] { Comma, Sp, D(x) })]), CloseBracket);
    private static Formula ReplicaArguments(Formula body) => All(V("n"), Nat, All(V("q"), Nat,
        Instance(Call("NeZero", V("n")), All(V("N"), Nat, All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))), All(Psi, State, body))))));
    private static Formula PartyArguments(Formula body) => All(V("n"), Nat,
        Instance(Call("NeZero", V("n")), All(V("N"), Nat, All(V("party"), Arrow(Fin(V("N")), Fin(D(4))), All(Psi, State, body)))));
    private static Formula Bits => Arrow(Fin(V("N")), Fin(D(2)));
    private static Formula State => Arrow(Bits, Complex);
    private static Formula Replicas(Formula n, Formula q) => Arrow(Fin(Difference(q, D(1))), Call("ZMod", n));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula statement,
        string explanation, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), provenance,
            Blocks(Paragraph(Text(explanation))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula name, Formula type) => Parenthesized(Seq(name, Sp, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, Parenthesized(b));
    private static Formula ImpP(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Rightarrow, Sp, Parenthesized(b));
    private static Formula Instance(Formula a, Formula b) => Seq(OpenBracket, a, CloseBracket, Comma, Sp, b);
    private static Formula Conj(Formula a, Formula b) => Seq(a, Sp, Land, Sp, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Difference(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Minus, Sp, b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumOver(Formula i, Formula x) => Seq(Sum, Underscore, Grp(i), Sp, x);
    private static Formula ProdOver(Formula i, Formula x) => Seq(Prod, Underscore, Grp(i), Sp, x);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => Seq(f, Open, Arguments(args), Close);
    private static Formula Add(params Formula[] summands) => Seq([.. summands.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Sp, Plus, Sp, x })]);
    private static Formula Arguments(Formula[] args) => Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x })]);
}
