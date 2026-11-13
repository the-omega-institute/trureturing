using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class ReversibleQramDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Routing/ReversibleQram.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/arunachalam2015robustness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reversible Boolean routing network selects one memory leaf, restores its workspace, "
            + "and acts coherently on arbitrary complex amplitudes.",
        H("Reversible QRAM routing and coherent readout"),
        Blocks(
            Paragraph(Text(
                "Addresses are binary words of any natural length n. Address 0 has one empty word; "
                    + "Address (n + 1) is Bool times Address n. Wires 0 is one Boolean wire, and "
                    + "Wires (n + 1) consists of two Wires n registers. The leftmost wire is the root "
                    + "input. The state clean n e puts e at that root and false at every scratch wire. "
                    + "The layout reuses each parent enable as its left output. Intermediate enables "
                    + "are therefore stored in place rather than retained in additional node registers.")),
            Describe.Lean(DescribeId.Create("qram-local-split"),
                DeclarationHandle.Create(Module + "split"), H("One routing split"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For address bit b, first XOR b AND the left root into the right root. "
                        + "Then XOR the resulting right root into the left root. These are the "
                        + "Toffoli and CNOT operations of Section IV. Starting with root values "
                        + "(e,false), their outputs are (e AND NOT b,e AND b). Other wires are "
                        + "untouched by this split. With e true at the first level, the Toffoli "
                        + "reduces to the address-copy CNOT described there. Both gates are "
                        + "permutations on arbitrary dirty wire configurations."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-routing"),
                DeclarationHandle.Create(Module + "route"), H("The recursive gate network"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "At depth zero route is the identity. At depth n + 1 it applies split "
                        + "with the first address bit, then routes both subregisters using the "
                        + "remaining address. Thus the network is defined by local gates; its "
                        + "definition does not use the one-hot specification. The separate function "
                        + "oneHot places e at the addressed leaf and false at every other leaf. "
                        + "The function leaf reads an individual leaf, with false and true leading "
                        + "bits selecting the left and right subregisters."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-leaf-additions"),
                DeclarationHandle.Create(Module + "readLeaves"), H("Leaf-controlled additions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix a classical memory D from Address n to an additive commutative group G. "
                        + "At each leaf, its Boolean wire controls addition of that leaf's datum "
                        + "to the bus. A fork first reads its left subtree and then its right "
                        + "subtree into the same bus. Product equivalences only rearrange the "
                        + "register coordinates around those additions. The resulting permutation "
                        + "preserves every routing wire. The recursively defined readAmount is "
                        + "the sum of the enabled data, and describes the effect of this sequence. "
                        + "The paper's Boolean readout is the special case of addition modulo two; "
                        + "arbitrary additive commutative data groups are the extension used here."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-query"),
                DeclarationHandle.Create(Module + "query"), H("Compute, read, and uncompute"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The address controls route, the leaf additions follow, and the inverse "
                        + "route is then applied. The inverse reverses the order of the local "
                        + "gates. This composition defines query on all basis configurations, "
                        + "without an initialization hypothesis. For dirty wires w, it preserves "
                        + "the address and w and adds readAmount n D (route n a w) to the bus. "
                        + "For clean n true, this amount is exactly D(a)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-matrix"),
                DeclarationHandle.Create(Module + "queryMatrix"), H("The complex query matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For finite G with decidable equality, queryMatrix is Mathlib's "
                        + "Matrix.permMatrixHom applied directly to query. Its rows and columns "
                        + "are indexed by Address n times (Wires n times G). The homomorphism "
                        + "uses the inverse permutation: forward movement of basis states "
                        + "therefore acts on amplitudes by pullback along the inverse. "
                        + "The function initialized embeds an arbitrary complex amplitude "
                        + "function on Address n times G into the full basis by making it "
                        + "zero whenever the routing workspace differs from clean n true."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-correctness"),
                DeclarationHandle.Create(Module + "correctness"),
                H("Correctness at every natural depth"), StatementSource.FromAuthor(CorrectnessFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural n, every address a, every leaf i and either Boolean "
                            + "enable e, routing clean n e gives leaf value e when i = a and "
                            + "false otherwise. In particular an enabled root produces exactly "
                            + "one excited leaf, and a disabled root produces only zero leaves. "
                            + "The empty address at n = 0 is included. The proof inducts through "
                            + "the actual split and both recursive gate networks.")),
                    Paragraph(Text(
                        "For every additive commutative G, memory D, address a, dirty workspace "
                            + "w and initial bus r, query preserves a and w and changes the bus "
                            + "to r + readAmount n D (route n a w). For w = clean n true it "
                            + "changes the bus to r + D(a), restoring every scratch wire and the "
                            + "root enable. The readout proof follows the successive additions; "
                            + "the routing induction supplies the addressed datum.")),
                    Paragraph(Text(
                        "For every finite additive commutative G with decidable equality and "
                            + "every D, queryMatrix has both adjoint products equal to the identity. "
                            + "For every complex amplitude function psi on Address n times G, "
                            + "multiplying initialized psi by queryMatrix yields initialized "
                            + "of the function (a,r) mapped to psi(a,r - D(a)). This is the exact "
                            + "coherent action for arbitrary superpositions of addresses and bus "
                            + "values. It preserves support on the initialized routing workspace. "
                            + "Unitarity and the inverse-permutation action use the pinned "
                            + "permutation-matrix identities directly.")),
                    Paragraph(Text(
                        "The memory D is fixed classical data. These statements concern an ideal "
                            + "reversible Boolean circuit and its complex linear action. They "
                            + "establish no physical locality of the bus, noise guarantee, primitive "
                            + "gate count or depth, three-state router implementation, or copying "
                            + "of unknown quantum memories. Section IV itself warns that its bus "
                            + "interacts with all memory bits. Page-Wootters claims and the original "
                            + "three-state bucket-brigade construction require separate arguments."))),
                DescribeRole.Theorem))));

    private static Formula CorrectnessFormula() => Disp(new Formula.Aligned([
        All("n", Naturals(), All("a", Addresses(), All("i", Addresses(), All("e", Q("Bool"),
            Equal(Call("leaf", X("n"), Call("route", X("n"), X("a"), Clean(X("e"))), X("i")),
                At(Q("ite"), Equal(X("i"), X("a")), X("e"), Q("Bool", "false"))))))),
        DataAll(All("a", Addresses(), All("w", Call("Wires", X("n")), All("r", X("G"),
            Equal(Call("query", X("n"), X("D"), Pair(X("a"), Pair(X("w"), X("r")))),
                Pair(X("a"), Pair(X("w"), Add(X("r"), Call("readAmount", X("n"), X("D"),
                    Call("route", X("n"), X("a"), X("w")))))))))), false),
        DataAll(All("a", Addresses(), All("r", X("G"),
            Equal(Call("query", X("n"), X("D"), Pair(X("a"), Pair(Clean(Q("Bool", "true")), X("r")))),
                Pair(X("a"), Pair(Clean(Q("Bool", "true")), Add(X("r"), At(X("D"), X("a")))))))), false),
        DataAll(And(Equal(Mul(Adj(Matrix()), Matrix()), D(1)),
            And(Equal(Mul(Matrix(), Adj(Matrix())), D(1)),
                All("psi", Arrow(PairType(Addresses(), X("G")), Complexes()),
                    Equal(At(Q("Matrix", "mulVec"), Matrix(), Call("initialized", X("n"), X("psi"))),
                        Call("initialized", X("n"),
                            LambdaOf("s", PairType(Addresses(), X("G")),
                                At(X("psi"), Pair(At(Q("Prod", "fst"), X("s")),
                                    Sub(At(Q("Prod", "snd"), X("s")),
                                        At(X("D"), At(Q("Prod", "fst"), X("s")))))))))))), true)
    ]));

    private static Formula DataAll(Formula body, bool finite)
    {
        var result = All("D", Arrow(Addresses(), X("G")), body);
        if (finite)
            result = All("F", At(Q("Fintype"), X("G")),
                All("E", At(Q("DecidableEq"), X("G")), result));
        return All("n", Naturals(), All("G", Q("Type"),
            All("A", At(Q("AddCommGroup"), X("G")), result)));
    }

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
    private static Formula Call(string name, params Formula[] args) =>
        At(Q("D5", "S3", "Quantum", "Routing", "ReversibleQram", name), args);
    private static Formula Addresses() => Call("Address", X("n"));
    private static Formula Clean(Formula e) => Call("clean", X("n"), e);
    private static Formula Matrix() => Call("queryMatrix", X("n"), X("D"));
    private static Formula Adj(Formula value) => At(Q("Matrix", "conjTranspose"), value);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula PairType(Formula left, Formula right) => Seq(Open, left, Sp, Times, Sp, right, Close);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, X(name), Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Open, X(name), Colon, Sp, type, Close, Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
}
