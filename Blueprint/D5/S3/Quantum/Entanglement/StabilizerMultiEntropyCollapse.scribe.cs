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
            Entry("shift", "shift", "Shifting a replica coordinate", ShiftFormula(),
                "Replica labels are functions Fin(q − 1) → ℤ/nℤ. The shift adds one at the coordinate whose natural index equals the colour c. Colour q − 1 has no such coordinate and acts as the identity. Natural differences such as q − 1 and q − 2 in these formulas use truncated subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("partition-function", "Z", "Contracting the replicas", PartitionFunction(),
                "A configuration x assigns a binary N-qubit string to each replica label r. The conjugated amplitude is evaluated at x(r); the other amplitude takes qubit u from the replica shifted by its colour col(u). Summing the product gives the computational-basis contraction of Appendix A.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("entropy", "S", "The normalized multi-entropy", Entropy(),
                "The normalization divides Z(n,q,col,ψ) by the indicated power of Z(1,q,col,ψ). The logarithm is applied to the real part of the quotient, with the prefactors specified in Appendix A. The casts of n to ℝ appear explicitly.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("tripartite-information", "I3", "Four cuts minus three cuts", TripartiteInformation(),
                "Label A, B, C, D by 0, 1, 2, 3. Each displayed tuple is a function from Fin 4 to the stated colour set, composed with party. In order, the four positive terms are ABC:D, ABD:C, ACD:B and BCD:A; the three subtracted terms are AB:CD, AC:BD and AD:BC. This is the Rényi tripartite information I₍₃,n₎ in Eq. (1) of the paper.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("genuine-entropy", "GM4", "The genuine four-party combination", GenuineEntropy(),
                "The six three-colour tuples merge AB, AC, AD, BC, BD and CD, respectively. Their entropies have coefficient −1/3, while the four singleton cuts have coefficient 1/3. The remaining term is −a times the tripartite information, for an arbitrary real parameter a, as in §2 of the paper.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("collapse-proposition", "claim", "Positivity and the n = 3 collapse", CollapseClaim(),
                "The proposition quantifies over every qubit count, every assignment to four labelled parties and every amplitude. Its two assumptions are Pauli stabilization and unit squared norm. The first conclusion includes every colour count and colouring and asserts both strict positivity of the real part and a zero imaginary part. The second conclusion is Eq. (3) for every real a, with I₃ interpreted as I₍₃,₃₎. Empty parties are allowed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("collapse", "result", "The stabilizer collapse", V("claim"),
                "A stabilizer state is a scalar multiple of a local-unitary image of a graph amplitude. Replica contractions are unchanged by the identical local unitaries on all copies. For graph amplitudes, the ternary translation form decomposes into bilinear blocks indexed by opposite nonzero Fourier modes. A block contributes the inverse power of two determined by its rank, giving positive real contractions. Each rank depends on the partition of the four party labels induced by its mode. The weighted counts of these partitions give the coefficient 1/9, establishing the displayed identity and the counting argument asked for in §6.",
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

    private static Formula Entropy() => ReplicaArguments(Equal(Call("S", V("n"), V("q"), V("col"), Psi),
        Multiply(Multiply(Fraction(D(1), Parenthesized(Seq(D(1), Sp, Minus, Sp, Typed(V("n"), Real)))),
                Fraction(D(1), Pow(Typed(V("n"), Real), Difference(V("q"), D(2))))),
            Call("log", Call("Re", Fraction(Call("Z", V("n"), V("q"), V("col"), Psi),
                Pow(Call("Z", D(1), V("q"), V("col"), Psi), Pow(V("n"), Difference(V("q"), D(1))))))))));

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
                Imp(Equal(SumOver(Typed(V("x"), Bits), Pow(new Formula.Norm(Apply(Psi, V("x"))), D(2))), D(1)),
                    Conj(Parenthesized(All(V("q"), Nat, All(V("col"), Arrow(Fin(V("N")), Fin(V("q"))),
                            Conj(Seq(D(0), Sp, Lt, Sp, Call("Re", Call("Z", D(3), V("q"), V("col"), Psi))),
                                Equal(Call("Im", Call("Z", D(3), V("q"), V("col"), Psi)), D(0)))))),
                        All(V("a"), Real, Equal(Call("GM4", D(3), V("a"), V("party"), Psi),
                            Multiply(Seq(Minus, Parenthesized(Seq(V("a"), Sp, Minus, Sp, Fraction(D(1), D(9))))),
                                Call("I3", D(3), V("party"), Psi))))))))))));

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
