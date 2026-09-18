using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class LoopyEvaluatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Combinatorics/LoopyEvaluator.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/kirillov2026loopy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete labelled evaluator realizes the ordinary Loopy polynomial and its source recursion laws.",
        H("The Concrete Loopy Evaluator"),
        Blocks(
            Paragraph(Text(
                "A pending edge is an ordered endpoint pair used to encode an undirected edge occurrence. "
                + "The edge list retains parallel occurrences. A self-pair is a pending loop, and the "
                + "separate accumulator stores loops already consumed by the recursion. The definitions "
                + "below all belong to this source module even though Lean uses the shared "
                + "LoopyDegreeSequence namespace.")),
            Def("edge", "Pending edge occurrences", "Edge",
                "Edge is Nat x Nat. The two coordinates are endpoint labels; orientation is representation data, not graph data."),
            Def("loopy-polynomial", "The ordinary Loopy polynomial ring", "LoopyPolynomial",
                "LoopyPolynomial is the multivariate polynomial ring, indexed by natural loop counts, over univariate integer polynomials in the deletion variable."),
            Def("valid", "Valid finite graph encodings", "Valid",
                "Valid V E ell says that both endpoints of every occurrence in E lie in V and that ell is zero outside V. It imposes no simplicity, connectedness, nonemptiness or looplessness condition."),
            Def("contract-vertex", "Contract one endpoint label", "contractVertex",
                "contractVertex a b sends b to a and fixes every other label."),
            Def("contract-edge", "Contract a pending occurrence", "contractEdge",
                "contractEdge applies contractVertex a b to both endpoints, so remaining parallel copies and loops are transported occurrence by occurrence."),
            Def("add-loop", "Accumulate one pending loop", "addLoop",
                "addLoop ell a updates only coordinate a from ell(a) to ell(a)+1."),
            Def("contract-loops", "Merge loop data during contraction", "contractLoops",
                "contractLoops ell a b puts ell(a)+ell(b)+1 at a, puts zero at discarded label b, and fixes all other coordinates. The added one retains the selected nonloop edge occurrence as a loop."),
            Def("relabel-edge", "Relabel one pending occurrence", "relabelEdge",
                "relabelEdge transports both endpoints along an ambient permutation."),
            Def("relabel-loops", "Relabel accumulated loops", "relabelLoops",
                "relabelLoops transports the accumulator contravariantly along the same permutation."),
            Def("union-loops", "Combine disjoint loop accumulators", "unionLoops",
                "unionLoops is pointwise addition; Valid and disjointness ensure that it represents the disjoint union."),
            Def("loopy-aux", "Deletion-contraction on occurrences", "loopyAux",
                "With no pending edges, loopyAux is the product over all retained vertices of x indexed by the accumulated loop count, including x_0 for an isolate. A pending loop is moved into the accumulator. A selected nonloop contributes the sum of its contraction branch and t times its deletion branch; contraction erases the second vertex and retains the selected occurrence as an accumulated loop."),
            Def("loopy", "The concrete ordinary Loopy evaluator", "loopy",
                "loopy is loopyAux with the same finite carrier, occurrence list and loop accumulator; its default accumulator is identically zero."),
            Theorem("loopy-spec", "Representation independence and the seven evaluator laws", "loopy_spec",
                "The seven visible clauses are: permutation relabelling invariance; endpoint-orientation invariance under Valid; adjacent occurrence exchange under Valid; pending-loop transfer; invariance under any list permutation under Valid; the arbitrary selected-occurrence loop/deletion-contraction recurrence; and multiplication on disjoint unions. These clauses formalize Definition 1.1 and Proposition 2.1 in the labelled list representation. The proof of their representation bridge is repository-derived."))));

    private static DocumentBlock Def(string id, string title, string name, string prose) =>
        Describe.Lean(DescribeId.Create("loopy-evaluator-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(DefinitionFormula(name)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string title, string name, string prose) =>
        Describe.Lean(DescribeId.Create("loopy-evaluator-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(LoopySpecFormula()),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula LoopySpecFormula()
    {
        var nat = I("Nat");
        var edge = I("Edge");
        var finsetNat = App("Finset", nat);
        var listEdge = App("List", edge);
        var loops = Seq(nat, Sp, To, Sp, nat);
        var perm = App("EquivPerm", nat);
        var p = All("f", perm, All("V", finsetNat, All("E", listEdge, All("ell", loops,
            Equal(
                Call("loopy", Call("map", Call("toEmbedding", I("f")), I("V")),
                    Call("map", Call("relabelEdge", I("f")), I("E")),
                    Call("relabelLoops", I("f"), I("ell"))),
                Call("loopy", I("V"), I("E"), I("ell")))))));
        var orientation = All("V", finsetNat, All("E", listEdge, All("ell", loops,
            All("a", nat, All("b", nat, Implies(
                Call("Valid", I("V"), Call("cons", Pair(I("a"), I("b")), I("E")), I("ell")),
                Equal(Call("loopy", I("V"), Call("cons", Pair(I("a"), I("b")), I("E")), I("ell")),
                    Call("loopy", I("V"), Call("cons", Pair(I("b"), I("a")), I("E")), I("ell")))))))));
        var adjacent = All("V", finsetNat, All("E", listEdge, All("ell", loops,
            All("e", edge, All("f", edge, Implies(
                Call("Valid", I("V"), Call("cons", I("e"), Call("cons", I("f"), I("E"))), I("ell")),
                Equal(Call("loopy", I("V"), Call("cons", I("e"), Call("cons", I("f"), I("E"))), I("ell")),
                    Call("loopy", I("V"), Call("cons", I("f"), Call("cons", I("e"), I("E"))), I("ell")))))))));
        var pendingLoop = All("V", finsetNat, All("E", listEdge, All("ell", loops, All("a", nat,
            Equal(Call("loopy", I("V"), Call("cons", Pair(I("a"), I("a")), I("E")), I("ell")),
                Call("loopy", I("V"), I("E"), Call("addLoop", I("ell"), I("a"))))))));
        var anyPermutation = All("V", finsetNat, All("E", listEdge, All("Eprime", listEdge,
            All("ell", loops, Implies(Call("Perm", I("E"), I("Eprime")),
                Implies(Call("Valid", I("V"), I("E"), I("ell")),
                    Equal(Call("loopy", I("V"), I("E"), I("ell")),
                        Call("loopy", I("V"), I("Eprime"), I("ell")))))))));
        var recurrenceRhs = Seq(I("if"), Sp, App("fst", I("e")), Eq, App("snd", I("e")),
            Sp, I("then"), Sp,
            Call("loopy", I("V"), I("R"), Call("addLoop", I("ell"), App("fst", I("e")))),
            Sp, I("else"), Sp,
            Add(Call("loopy", Call("erase", I("V"), App("snd", I("e"))),
                    Call("map", Call("contractEdge", App("fst", I("e")), App("snd", I("e"))), I("R")),
                    Call("contractLoops", I("ell"), App("fst", I("e")), App("snd", I("e")))),
                Multiply(App("C", I("t")), Call("loopy", I("V"), I("R"), I("ell")))));
        var recurrence = All("V", finsetNat, All("E", listEdge, All("R", listEdge, All("ell", loops,
            All("e", edge, Implies(Call("Perm", I("E"), Call("cons", I("e"), I("R"))),
                Implies(Call("Valid", I("V"), I("E"), I("ell")),
                    Equal(Call("loopy", I("V"), I("E"), I("ell")), recurrenceRhs))))))));
        var disjointUnion = All("Vone", finsetNat, All("Vtwo", finsetNat,
            All("Eone", listEdge, All("Etwo", listEdge, All("ellone", loops, All("elltwo", loops,
                Implies(Call("Disjoint", I("Vone"), I("Vtwo")),
                    Implies(Call("Valid", I("Vone"), I("Eone"), I("ellone")),
                        Implies(Call("Valid", I("Vtwo"), I("Etwo"), I("elltwo")),
                            Equal(
                                Call("loopyAux", Call("union", I("Vone"), I("Vtwo")),
                                    Call("append", I("Eone"), I("Etwo")),
                                    Call("unionLoops", I("ellone"), I("elltwo"))),
                                Multiply(Call("loopyAux", I("Vone"), I("Eone"), I("ellone")),
                                    Call("loopyAux", I("Vtwo"), I("Etwo"), I("elltwo")))))))))))));
        return Disp(And(p, And(orientation, And(adjacent, And(pendingLoop,
            And(anyPermutation, And(recurrence, disjointUnion)))))));
    }

    private static Formula DefinitionFormula(string name) => name switch
    {
        "Edge" => Eqn(I("Edge"), Seq(I("Nat"), Sp, Times, Sp, I("Nat"))),
        "LoopyPolynomial" => Eqn(I("LoopyPolynomial"),
            App("MvPolynomial", I("Nat"), App("Polynomial", I("Int")))),
        "Valid" => Eqn(Call("Valid", I("V"), I("E"), I("ell")),
            And(
                AllIn("e", I("E"), And(
                    InSet(App("fst", I("e")), I("V")),
                    InSet(App("snd", I("e")), I("V")))),
                All("v", Implies(
                    Seq(Neg, Sp, InSet(I("v"), I("V"))),
                    Equal(Call("ell", I("v")), D(0)))))),
        "contractVertex" => Eqn(Call("contractVertex", I("a"), I("b"), I("v")),
            Seq(I("if"), Sp, I("v"), Sp, Eq, Sp, I("b"), Sp, I("then"), Sp,
                I("a"), Sp, I("else"), Sp, I("v"))),
        "contractEdge" => Eqn(Call("contractEdge", I("a"), I("b"), I("e")),
            Pair(Call("contractVertex", I("a"), I("b"), App("fst", I("e"))),
                Call("contractVertex", I("a"), I("b"), App("snd", I("e"))))),
        "addLoop" => Eqn(Call("addLoop", I("ell"), I("a")),
            Call("update", I("ell"), I("a"),
                Add(Call("ell", I("a")), D(1)))),
        "contractLoops" => Eqn(Call("contractLoops", I("ell"), I("a"), I("b"), I("v")),
            Seq(I("if"), Sp, I("v"), Eq, I("a"), Sp, I("then"), Sp,
                Add(Add(Call("ell", I("a")), Call("ell", I("b"))), D(1)), Sp,
                I("else"), Sp, I("if"), Sp, I("v"), Eq, I("b"), Sp, I("then"), Sp,
                D(0), Sp, I("else"), Sp, Call("ell", I("v")))),
        "relabelEdge" => Eqn(Call("relabelEdge", I("f"), I("e")),
            Pair(Call("f", App("fst", I("e"))), Call("f", App("snd", I("e"))))),
        "relabelLoops" => Eqn(Call("relabelLoops", I("f"), I("ell"), I("v")),
            Call("ell", Apply(Inverse(I("f")), I("v")))),
        "unionLoops" => Eqn(Call("unionLoops", I("ellone"), I("elltwo"), I("v")),
            Add(Call("ellone", I("v")), Call("elltwo", I("v")))),
        "loopyAux" => LoopyAuxFormula(),
        "loopy" => Eqn(Call("loopy", I("V"), I("E"), I("ell")),
            Call("loopyAux", I("V"), I("E"), I("ell"))),
        _ => throw new ArgumentOutOfRangeException(nameof(name))
    };

    private static Formula LoopyAuxFormula()
    {
        var baseCase = Equal(
            Call("loopyAux", I("V"), I("nil"), I("ell")),
            Seq(Prod, Underscore, Grp(Seq(I("v"), Sp, InMacro, Sp, I("V"))), Sp,
                App("X", Call("ell", I("v")))));
        var loopCase = Call("loopyAux", I("V"), I("E"),
            Call("addLoop", I("ell"), I("a")));
        var nonloopCase = Add(
            Call("loopyAux", Call("erase", I("V"), I("b")),
                Call("map", Call("contractEdge", I("a"), I("b")), I("E")),
                Call("contractLoops", I("ell"), I("a"), I("b"))),
            Multiply(App("C", I("t")), Call("loopyAux", I("V"), I("E"), I("ell"))));
        var step = Equal(
            Call("loopyAux", I("V"), App("cons", Pair(I("a"), I("b")), I("E")), I("ell")),
            Seq(I("if"), Sp, I("a"), Eq, I("b"), Sp, I("then"), Sp, loopCase,
                Sp, I("else"), Sp, nonloopCase));
        return Disp(Seq(baseCase, Comma, Sp, step));
    }

    private static Formula I(string value) => F.Id(value);
    private static Formula Named(string value) => Seq(Operatorname, Grp(I(value)));
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Inverse(Formula value) =>
        Seq(value, Caret, Grp(Seq(Minus, D(1))));
    private static Formula Call(string name, params Formula[] args) => App(name, args);
    private static Formula Eqn(Formula left, Formula right) => Disp(Equal(left, right));
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Multiply(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);
    private static Formula Implies(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Rightarrow, Sp, Open, right, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula InSet(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula All(string variable, Formula body) =>
        Seq(Forall, Sp, I(variable), Comma, Sp, body);
    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, I(variable), Colon, Sp, type, Comma, Sp, body);
    private static Formula AllIn(string variable, Formula set, Formula body) =>
        Seq(Forall, Sp, I(variable), Sp, InMacro, Sp, set, Comma, Sp, body);
}
