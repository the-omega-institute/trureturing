using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class HannSpatialQramDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Routing/HannSpatialQram.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumRouting/hann2021resilience");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sequential address absorption and local qutrit transport implement clean classical-bit "
            + "lookup at every natural depth, with exact complex linear action.",
        H("Sequential spatial qutrit QRAM"),
        Blocks(
            Paragraph(Text(
                "The model follows Hann, Lee, Girvin and Jiang, Section II.B and Figure 1(b), "
                    + "Appendix A and Figure 10, and Appendix B equation (B1). Qutrit has three "
                    + "basis labels: wait W, zero and one. encode maps either Boolean to its "
                    + "occupied label. W is router wait and spatial vacuum in this model. "
                    + "Address n is the existing recursive binary word: Unit at zero and Bool "
                    + "times Address n at a successor. bit reads its bits in head-first order.")),
            Def("spatial-coordinates", "Interior", "Actual rails and routers",
                "Tree n is Qutrit times Interior n: its first coordinate is the incident rail. "
                    + "Interior 0 is Unit, so depth zero has one spatial leaf and no router. "
                    + "Interior (n+1) contains one router and two Tree n children. Each child's "
                    + "incident rail is exactly its parent's corresponding output rail. State n "
                    + "contains n distinct qutrit address slots, one distinct external bus, and "
                    + "Tree n. vacuum initializes every router and mode to W. input replaces "
                    + "only the tree's incident coordinate."),
            Def("spatial-local-gates", "route", "Full SWAP and controlled full SWAP",
                "absorb swaps incident and router labels on their full three-level spaces. "
                    + "leftGate swaps incident and the left output exactly when the router is "
                    + "zero; rightGate swaps incident and the right output exactly when it is "
                    + "one. route applies these two gates in that order. All other coordinates "
                    + "are preserved. These are literal permutations on arbitrary dirty basis "
                    + "states, constructed by the existing involution-to-permutation API. "
                    + "children applies specified operations in both subtrees, leaving the "
                    + "parent incident and router unchanged. No gate is selected by an "
                    + "externally supplied address value."),
            Def("spatial-sequential-loading", "load", "Sequential address absorption",
                "descend n k routes through k existing router levels and performs absorption "
                    + "SWAPs at that depth; the same recursive schedule acts in both subtrees. "
                    + "At zero tree depth descend is inert. inject exchanges address slot k "
                    + "with the root incident rail and preserves every other slot and the bus. "
                    + "load n k is the composition of the first k injections, each followed "
                    + "by descend at the appropriate depth. Steps beyond n are inert. "
                    + "The circuit schedule depends on indices and depth, never on address data."),
            Def("spatial-prefix-state", "loading", "The dynamic prefix invariant",
                "remaining n a k puts W in slots with index less than k and retains the "
                    + "encoded address bit in every other slot. programmed n a k puts the "
                    + "first k address bits in the routers on a's prefix path, with all "
                    + "other routers and every spatial mode W. loading combines remaining, "
                    + "an arbitrary unchanged external bus label, and programmed. "
                    + "The local induction shows that descend sends the next incident "
                    + "address bit into its waiting router, extends this prefix by one, "
                    + "and leaves the incident and output rails vacuum. The other subtree "
                    + "remains vacuum. Induction over injections proves the stated loading "
                    + "invariant for every k at most n."),
            Def("spatial-payload", "transport", "One payload through adjacent modes",
                "transport applies route at the root and recursively in both children. "
                    + "arrived n a p retains the fully programmed routers, puts p at spatial "
                    + "leaf a and W in every other mode. leaf observes an actual leaf rail. "
                    + "The operational induction transports an arbitrary incident label p "
                    + "through the programmed path into arrived. Its leaf equation makes "
                    + "the unique occupied payload explicit when p is zero or one; for "
                    + "p = W every spatial leaf is vacuum. All intermediate parent incident "
                    + "rails are cleared by their local exchange with the selected child."),
            Def("spatial-leaf-readout", "readLeaves", "Vacuum-preserving local readout",
                "Fix classical memory D from Address n to Bool. dataGate is identity for "
                    + "false and swaps zero and one for true, fixing W in either case. "
                    + "This is precisely X-tilde from equation (B1). readLeaves applies the "
                    + "appropriate fixed dataGate at every spatial leaf, leaving internal "
                    + "router and incident coordinates unchanged. On arrived, every "
                    + "unoccupied leaf remains W and the unique payload becomes "
                    + "encode (b XOR D(a)). There is no address-selected memory operation."),
            Def("spatial-query", "query", "Read and reverse the actual circuit",
                "forward loads all n address signals, swaps the external bus with the root "
                    + "incident rail, and transports it to a spatial leaf. query applies "
                    + "forward, readLeaves on the spatial tree, and the exact inverse of "
                    + "forward. clean is loading with k = 0 and external bus encode b. "
                    + "The loading and transport inductions identify forward(clean) with "
                    + "all address slots W, the external bus W, and arrived. Local readout "
                    + "changes only the occupied payload. The inverse restores each "
                    + "address slot, the external bus position, every router to wait and "
                    + "every spatial rail to vacuum."),
            Def("spatial-linear-action", "queryMatrix", "Complex linear action",
                "queryMatrix is Mathlib's Matrix.permMatrixHom applied directly to query. "
                    + "initialized psi is the finite sum over all addresses and encoded bus "
                    + "bits of psi(a,b) at clean n a b, and zero contributions elsewhere. "
                    + "The matrix is unitary. Its inverse-permutation pullback sends these "
                    + "amplitudes to psi(a,b XOR D(a)), for arbitrary complex psi. This "
                    + "uses the existing permutation-matrix identities and the clean "
                    + "circuit theorem directly."),
            Describe.Lean(DescribeId.Create("spatial-correctness"),
                DeclarationHandle.Create(Module + "correctness"),
                H("All-depth sequential spatial lookup"),
                StatementSource.FromAuthor(CorrectnessFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The four clauses give prefix loading at every intermediate k, the "
                            + "exact transport state and its leaf observations, clean XOR "
                            + "lookup for both bus values, and both adjoint identities with "
                            + "the complex-amplitude action. All natural depths include zero: "
                            + "there are no address slots or routers there, but the external "
                            + "bus swaps into a unique spatial leaf, reads it and returns.")),
                    Paragraph(Text(
                        "These statements formalize the published ideal three-level "
                            + "construction under the ordinary sequential address schedule. "
                            + "They do not identify its dirty-state permutation with the "
                            + "pipelined Figure 10 ordering. The original 0708.1879 fiducial "
                            + "qubit f is not identified with W. The existing Boolean "
                            + "ReversibleQram network supplies address types, not spatial "
                            + "dynamics. No depth, gate-count, noise, energy or global "
                            + "superposition activation bound, microscopic Hamiltonian or "
                            + "copying of unknown quantum data follows from these claims."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula CorrectnessFormula()
    {
        var loading = All("n", Naturals(), All("a", Addresses(),
            All("b", Call("Qutrit"), All("k", Naturals(),
                Imp(Le(X("k"), X("n")), Equal(
                    At(Call("load", X("n"), X("k")),
                        Call("loading", X("n"), X("a"), X("b"), D(0))),
                    Call("loading", X("n"), X("a"), X("b"), X("k"))))))));
        var leafValue = At(Q("ite"), Equal(X("i"), X("a")), X("p"),
            Q("D5", "S3", "Quantum", "Routing", "HannSpatialQram", "Qutrit", "wait"));
        var transport = All("n", Naturals(), All("a", Addresses(), All("p", Call("Qutrit"),
            And(Equal(Transport(), Call("arrived", X("n"), X("a"), X("p"))),
                All("i", Addresses(), Equal(Call("leaf", X("n"), Transport(), X("i")), leafValue))))));
        var lookup = DataAll(All("a", Addresses(), All("b", Q("Bool"), Equal(
            At(Call("query", X("n"), X("D")), Call("clean", X("n"), X("a"), X("b"))),
            Call("clean", X("n"), X("a"), Xor(X("b"), At(X("D"), X("a"))))))));
        var stateType = PairType(Addresses(), Q("Bool"));
        var address = At(Q("Prod", "fst"), X("s"));
        var bus = At(Q("Prod", "snd"), X("s"));
        var pulled = LambdaOf("s", stateType,
            At(X("psi"), Pair(address, Xor(bus, At(X("D"), address)))));
        var action = All("psi", Arrow(stateType, Complexes()),
            Equal(At(Q("Matrix", "mulVec"), Matrix(), Call("initialized", X("n"), X("psi"))),
                Call("initialized", X("n"), pulled)));
        var linear = DataAll(And(Equal(Mul(Adj(Matrix()), Matrix()), D(1)),
            And(Equal(Mul(Matrix(), Adj(Matrix())), D(1)), action)));
        return Rows([loading, transport, lookup, linear]);
    }

    private static Formula DataAll(Formula body) => All("n", Naturals(),
        All("D", Arrow(Addresses(), Q("Bool")), body));
    private static Formula Transport() => At(Call("transport", X("n")),
        Call("input", X("n"), Call("programmed", X("n"), X("a"), X("n")), X("p")));
    private static Formula Addresses() => At(Q("D5", "S3", "Quantum", "Routing", "ReversibleQram", "Address"), X("n"));
    private static Formula Matrix() => Call("queryMatrix", X("n"), X("D"));
    private static Formula Adj(Formula value) => At(Q("Matrix", "conjTranspose"), value);
    private static Formula Xor(Formula a, Formula b) => At(Q("Bool", "xor"), a, b);
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Call(string name, params Formula[] args)
    {
        var nameFormula = Q("D5", "S3", "Quantum", "Routing", "HannSpatialQram", name);
        return args.Length == 0 ? nameFormula : At(nameFormula, args);
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Rows(Formula[] clauses) => new Formula.Aligned([
        .. System.Linq.Enumerable.Select(clauses, (clause, index) => index == 0
            ? Seq(Open, clause, Close) : Seq(Land, Sp, Open, clause, Close))]);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula PairType(Formula a, Formula b) => Seq(Open, a, Sp, Times, Sp, b, Close);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, X(name), Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Open, X(name), Colon, Sp, type, Close, Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
}
