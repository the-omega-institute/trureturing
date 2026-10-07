using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGroupChainPathsPrescribedArraysDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Quant(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Group(Formula body, bool ordered = false, bool finite = true) =>
        Quant(Seq(OpenBracket, Call("Group", Id("H")), CloseBracket,
            finite ? Seq(OpenBracket, Call("Fintype", Id("H")), CloseBracket) : Seq(),
            ordered ? Seq(OpenBracket, Call("LinearOrder", Id("H")), CloseBracket) : Seq(),
            body), B("H", Id("Type")));
    private static Formula FactorsAll(Formula body, bool ordered = false,
        bool finite = false, params Formula.BoundVariable[] extra) => Group(Quant(body,
            [B("n", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
            B("f", Call("Factors", Id("H"), Id("n"), Id("m"), Id("L"))),
            .. extra]), ordered, finite || ordered);
    private static Formula ChainAll(Formula body) => Group(Quant(body,
        B("n", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
        B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
        B("B", Call("GroupMat", Id("H"), Id("m"), Id("m"))),
        B("c", Call("Chain", Id("H"), Id("A"), Id("B"), Id("L")))));
    private static Formula And(Formula a, Formula b) =>
        Seq(Open, a, Land, Sp, b, Close);
    private static Formula Product => Call("factorProduct", Id("f"));
    private static Formula Path => Call("FactorPath", Id("f"), Id("i"), Id("j"));
    private static Formula Fiber => Call("FactorFiber", Id("f"), Id("i"), Id("j"), Id("g"));
    private static Formula Copies => Call("Fin", Call("coeff",
        Call("entry", Product, Id("i"), Id("j")), Id("g")));
    private static Formula.BoundVariable[] Endpoints =>
        [B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("m")))];
    private static Formula.BoundVariable[] EndpointsLabel =>
        [.. Endpoints, B("g", Id("H"))];
    private static DocumentBlock Item(string selector, string title, Formula statement,
        string paragraph, DescribeRole role) => Describe.Lean(
            DescribeId.Create("chainpaths-" + selector.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), role);

    private static Formula OrderedChainAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("n", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
            B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
            B("B", Call("GroupMat", Id("H"), Id("m"), Id("m"))),
            B("c", Call("Chain", Id("H"), Id("A"), Id("B"), Id("L"))), .. extra]), true);
    private static Formula Sig(string v, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sigma, Seq(Id(v), Colon, type)), Open, body, Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Times, b, Close);
    private static Formula At(Formula matrix, string i, string j) => Call("At", matrix, Id(i), Id(j));
    private static Formula FP(string factors, string i, string j) =>
        Call("FactorPath", Call(factors, Id("c")), Id(i), Id(j));
    private static Formula W(string matrix, Formula length, string i, string j) =>
        Call("Word", Id(matrix), length, Id(i), Id(j));
    private static Formula CB(bool dual = false) => Sig("v", Call("Fin", Id(dual ? "n" : "m")),
        Pair(FP(dual ? "backwardFactors" : "forwardFactors", "i", "v"),
            FP(dual ? "forwardFactors" : "backwardFactors", "v", "j")));
    private static Formula SweepIn(bool dual = false, bool ranked = false, Formula? length = null) =>
        Sig("x", Call("Fin", Id(dual ? "m" : "n")), Pair(
            length is null ? At(Id(dual ? "B" : "A"), "i", "x") : W(dual ? "B" : "A", length, "i", "x"),
            ranked ? At(Call(dual ? "S" : "R", Id("c")), "x", "j") :
                FP(dual ? "backwardFactors" : "forwardFactors", "x", "j")));
    private static Formula SweepOut(bool dual = false, bool ranked = false, Formula? length = null) =>
        Sig("y", Call("Fin", Id(dual ? "n" : "m")), Pair(
            ranked ? At(Call(dual ? "S" : "R", Id("c")), "i", "y") :
                FP(dual ? "backwardFactors" : "forwardFactors", "i", "y"),
            length is null ? At(Id(dual ? "A" : "B"), "y", "j") : W(dual ? "A" : "B", length, "y", "j")));
    private static Formula MapType(string name, Formula domain, Formula codomain, params Formula[] args) =>
        Seq(Call(name, args), Colon, Call("Equiv", domain, codomain));
    private static Formula Label(Formula f, Formula p) => Call("factorLabel", f, p);
    private static Formula First(Formula p) => Call("first", p);
    private static Formula Second(Formula p) => Call("second", p);
    private static Formula LabelOf(Formula p) => Call("label", p);
    private static Formula ApplyMap(string name, Formula p) => Call("apply", Call(name, Id("c"), Id("i"), Id("j")), p);
    private static Formula LongLaw(bool dual, bool ranked) => OrderedChainAll(Quant(
        Equal(Call(ranked ? (dual ? "matrixPhiSPower" : "matrixPhiRPower") : (dual ? "phiSPower" : "phiRPower"),
            Id("c"), Id("L"), Id("i"), Id("j"), Call("tuple", Id("x"),
                Call(ranked ? (dual ? "matrixPsiL" : "matrixPsi0") : (dual ? "psiL" : "psi0"),
                    Id("c"), Id("i"), Id("x"), Call("tuple", Id("y"), Id("r"), Id("s"))), Id("rp"))),
            Call("tuple", Id("y"), Id("r"),
                Call(ranked ? (dual ? "matrixPsi0" : "matrixPsiL") : (dual ? "psi0" : "psiL"),
                    Id("c"), Id("y"), Id("j"), Call("tuple", Id("x"), Id("s"), Id("rp"))))),
        B("i", Call("Fin", Id(dual ? "m" : "n"))), B("x", Call("Fin", Id(dual ? "m" : "n"))),
        B("y", Call("Fin", Id(dual ? "n" : "m"))), B("j", Call("Fin", Id(dual ? "n" : "m"))),
        B("r", ranked ? At(Call(dual ? "S" : "R", Id("c")), "i", "y") : FP(dual ? "backwardFactors" : "forwardFactors", "i", "y")),
        B("s", ranked ? At(Call(dual ? "R" : "S", Id("c")), "y", "x") : FP(dual ? "forwardFactors" : "backwardFactors", "y", "x")),
        B("rp", ranked ? At(Call(dual ? "S" : "R", Id("c")), "x", "j") : FP(dual ? "backwardFactors" : "forwardFactors", "x", "j"))));
    private static Formula.BoundVariable[] MapEndpoints(bool dual = false, bool square = false) =>
        [B("i", Call("Fin", Id(dual ? "m" : "n"))),
            B("j", Call("Fin", Id(square ? (dual ? "m" : "n") : (dual ? "n" : "m"))))];

    private static Formula RowAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("n", Id("Nat")), B("l", Id("Nat")),
            B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))), .. extra]), finite: false);
    private static Formula LocalRowAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("n", Id("Nat")), B("k", Id("Nat")), B("l", Id("Nat")),
            B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))),
            B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))),
            B("r", Call("NumberedRow", Multiply(Id("U"), Id("V")), Id("l"))), .. extra]), true);
    private static Formula PeelingRowAll(Formula body) =>
        Group(Quant(body, B("n", Id("Nat")), B("k", Id("Nat")), B("l", Id("Nat")),
            B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))),
            B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))),
            B("r", Call("NumberedRow", Multiply(Id("U"), Id("V")), Call("successor", Id("l")))),
            B("p", Call("G34FactorStep", Id("U"), Id("V"), Id("r")))), true);
    private static Formula ArraySuccAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("L", Id("Nat")), B("l", Id("Nat")),
            B("data", Call("IndexedChain", Id("H"), Call("successor", Id("L")))), .. extra]), true);
    private static Formula StepType => Call("G34Step", Id("A"), Id("B"), Id("U"), Id("V"), Id("hA"), Id("hB"), Id("r"));
    private static Formula StepAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("n", Id("Nat")), B("k", Id("Nat")), B("l", Id("Nat")),
            B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
            B("B", Call("GroupMat", Id("H"), Id("k"), Id("k"))),
            B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))),
            B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))),
            B("hA", Equal(Id("A"), Multiply(Id("U"), Id("V")))),
            B("hB", Equal(Id("B"), Multiply(Id("V"), Id("U")))),
            B("r", Call("NumberedRow", Id("A"), Id("l"))), .. extra]), true);
    private static Formula ArrayAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("L", Id("Nat")), B("l", Id("Nat")),
            B("data", Call("IndexedChain", Id("H"), Id("L"))), .. extra]), true);
    private static Formula SquareArrayAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("L", Id("Nat")),
            B("data", Call("IndexedChain", Id("H"), Id("L"))), .. extra]), true);
    private static Formula ArrayType => Call("G34Array", Id("data"), Id("l"));

        private static Formula UnorderedChainAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("n", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
            B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
            B("B", Call("GroupMat", Id("H"), Id("m"), Id("m"))),
            B("c", Call("Chain", Id("H"), Id("A"), Id("B"), Id("L"))), .. extra]));
    private static Formula BoundaryAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("L", Id("Nat")), B("data", Call("IndexedChain", Id("H"), Id("L"))), .. extra]));
public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prescribed finite arrays and ordered labels. All numbered edges, ordered labels and source conditions are retained.",
        H("Prescribed finite arrays and ordered labels"),
        Blocks(
            Item("rowFirst", "The rowFirst actual sweep",
                OrderedChainAll(MapType("rowFirst", SweepIn(false, false, length: Id("l")), SweepOut(false, false, length: Id("l")), Id("c"), Id("l"), Id("i"), Id("j")), [ B("l", Id("Nat")), .. MapEndpoints(false)]),
                "The same local transformations are evaluated one complete layer row at a time, always using the given factor path at the right boundary. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.", DescribeRole.Definition),
            Item("psi0_label", "Ordered total-label preservation",
                OrderedChainAll(Equal(Label(Call("wordFactors", Id("A"), Id("L")), ApplyMap("psi0", Id("p"))), Multiply(Label(Call("forwardFactors", Id("c")), First(Id("p"))), Label(Call("backwardFactors", Id("c")), Second(Id("p"))))), [.. MapEndpoints(false, true), B("p", CB(false))]),
                "The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.", DescribeRole.Theorem),
            Item("psiL_label", "Ordered total-label preservation",
                OrderedChainAll(Equal(Label(Call("wordFactors", Id("B"), Id("L")), ApplyMap("psiL", Id("p"))), Multiply(Label(Call("backwardFactors", Id("c")), First(Id("p"))), Label(Call("forwardFactors", Id("c")), Second(Id("p"))))), [.. MapEndpoints(true, true), B("p", CB(true))]),
                "The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.", DescribeRole.Theorem),
            Item("matrixPsi0_label", "Ordered total-label preservation",
                OrderedChainAll(Equal(Label(Call("wordFactors", Id("A"), Id("L")), ApplyMap("matrixPsi0", Id("p"))), Multiply(LabelOf(First(Id("p"))), LabelOf(Second(Id("p"))))), [.. MapEndpoints(false, true), B("p", Sig("v", Call("Fin", Id("m")), Pair(At(Call("R", Id("c")), "i", "v"), At(Call("S", Id("c")), "v", "j"))))]),
                "The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.", DescribeRole.Theorem),
            Item("matrixPsiL_label", "Ordered total-label preservation",
                OrderedChainAll(Equal(Label(Call("wordFactors", Id("B"), Id("L")), ApplyMap("matrixPsiL", Id("p"))), Multiply(LabelOf(First(Id("p"))), LabelOf(Second(Id("p"))))), [.. MapEndpoints(true, true), B("p", Sig("v", Call("Fin", Id("n")), Pair(At(Call("S", Id("c")), "i", "v"), At(Call("R", Id("c")), "v", "j"))))]),
                "The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.", DescribeRole.Theorem),
            Item("phiR_label", "Ordered total-label preservation",
                OrderedChainAll(Equal(Multiply(Label(Call("forwardFactors", Id("c")), First(ApplyMap("phiR", Id("p")))), LabelOf(Second(ApplyMap("phiR", Id("p"))))), Multiply(LabelOf(First(Id("p"))), Label(Call("forwardFactors", Id("c")), Second(Id("p"))))), [.. MapEndpoints(false, false), B("p", SweepIn(false, false))]),
                "The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.", DescribeRole.Theorem),
            Item("phiS_label", "Ordered total-label preservation",
                OrderedChainAll(Equal(Multiply(Label(Call("backwardFactors", Id("c")), First(ApplyMap("phiS", Id("p")))), LabelOf(Second(ApplyMap("phiS", Id("p"))))), Multiply(LabelOf(First(Id("p"))), Label(Call("backwardFactors", Id("c")), Second(Id("p"))))), [.. MapEndpoints(true, false), B("p", SweepIn(true, false))]),
                "The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.", DescribeRole.Theorem),
            Item("matrixPhiR_label", "Ordered total-label preservation",
                OrderedChainAll(Equal(Multiply(LabelOf(First(ApplyMap("matrixPhiR", Id("p")))), LabelOf(Second(ApplyMap("matrixPhiR", Id("p"))))), Multiply(LabelOf(First(Id("p"))), LabelOf(Second(Id("p"))))), [.. MapEndpoints(false, false), B("p", SweepIn(false, true))]),
                "The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.", DescribeRole.Theorem),
            Item("matrixPhiS_label", "Ordered total-label preservation",
                OrderedChainAll(Equal(Multiply(LabelOf(First(ApplyMap("matrixPhiS", Id("p")))), LabelOf(Second(ApplyMap("matrixPhiS", Id("p"))))), Multiply(LabelOf(First(Id("p"))), LabelOf(Second(Id("p"))))), [.. MapEndpoints(true, false), B("p", SweepIn(true, true))]),
                "The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.", DescribeRole.Theorem),
            Item("layerSweep", "One row with its prescribed right boundary",
                Group(Quant(MapType("layerSweep", Sig("x", Call("Fin", Id("n")), Pair(Call("Word", Call("product", Id("U"), Id("V")), Id("l"), Id("i"), Id("x")), At(Id("U"), "x", "j"))), Sig("y", Call("Fin", Id("k")), Pair(At(Id("U"), "i", "y"), Call("Word", Call("product", Id("V"), Id("U")), Id("l"), Id("y"), Id("j")))), Id("U"), Id("V"), Id("l"), Id("i"), Id("j")), B("n", Id("Nat")), B("k", Id("Nat")), B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))), B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))), B("l", Id("Nat")), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("k")))), true),
                "Apply the actual local cells from right to left along the row. The given U edge supplies the last cell at i=l-1, and each other cell reads the U edge just computed at its right neighbor. The reverse algorithm inverts the same cells in the opposite order.", DescribeRole.Definition),
            Item("NumberedRow", "A finite row with all numbered edges",
                RowAll(Seq(Call("NumberedRow", Id("A"), Id("l")), Colon, Id("Type"))),
                "A row consists of a vertex function x:Fin(l+1)→Fin n and, for each i:Fin l, an edge in At(A,x(i.castSucc),x(i.succ)). These are the literal vertices 0 through l and edges 0 through l−1. The length-zero row retains its named vertex.", DescribeRole.Definition),
            Item("rowHalves", "All U half-edges including the prescribed boundary",
                LocalRowAll(Seq(Call("rowHalves", Id("U"), Id("V"), Id("r"), Id("z"), Id("right")), Colon, Id("TypedUHalfEdges")), B("z", Call("Fin", Id("k"))), B("right", Call("At", Id("U"), Call("lastVertex", Id("r")), Id("z")))),
                "For r:NumberedRow(UV,l), z:Fin k and right:At(U,r.vertex(l),z), this dependent function assigns a target y_i and an actual U edge from r.vertex(i) to y_i for every i:Fin(l+1). At i<l it reads the prescribed ordered theta split of r.edge(i); at i=l it returns exactly z and right. In this formula lastVertex denotes r.vertex(Fin.last l), and A=UV.", DescribeRole.Definition),
            Item("nextNumberedRow", "The literal eta recurrence",
                LocalRowAll(Seq(Call("nextNumberedRow", Id("U"), Id("V"), Id("r"), Id("z"), Id("right")), Colon, Call("NumberedRow", Multiply(Id("V"), Id("U")), Id("l"))), B("z", Call("Fin", Id("k"))), B("right", Call("At", Id("U"), Call("lastVertex", Id("r")), Id("z")))),
                "For the factor row A=UV and B=VU, let (u_i,v_i)=theta inverse(r.edge(i)) for i<l and let u_l be the prescribed right edge. The next vertex at i is target(u_i). Its edge at i is eta(v_i,u_(i+1)). The target of v_i is the source of u_(i+1), including at i=l−1, so every edge has its actual legal endpoints.", DescribeRole.Definition),
            Item("G34Step", "A row and its actual recurrence laws",
                StepAll(Seq(StepType, Colon, Id("Type"))),
                "A step retains next:NumberedRow(B,l), all u_i:At(U,r.vertex(i),next.vertex(i)) for 0≤i≤l, and all v_i:At(V,next.vertex(i),r.vertex(i+1)) for 0≤i<l. Its theta law states theta inverse(r.edge(i))=(next.vertex(i),u_i,v_i), with the A=UV equality transporting the input type. Its eta law states next.edge(i)=eta(v_i,u_(i+1)), with B=VU transporting the output type. Every label and copy number belongs to these actual sigma coordinates.", DescribeRole.Definition),
            Item("generateG34Step", "Construct a legal row with its prescribed boundary",
                StepAll(Seq(Call("generateG34Step", Id("A"), Id("B"), Id("U"), Id("V"), Id("hA"), Id("hB"), Id("r"), Id("z"), Id("right")), Colon, StepType), B("z", Call("Fin", Id("k"))), B("right", Call("At", Id("U"), Call("lastVertex", Id("r")), Id("z")))),
                "The constructor applies the given ordered splits to all top edges and the given ordered joins to adjacent half-edges. It produces the complete G34Step and proves both displayed recurrence laws. Its final vertex is z and its final U edge is the supplied right edge, with only the necessary endpoint equality transport. Here lastVertex is r.vertex(Fin.last l).", DescribeRole.Definition),
            Item("G34Array", "The single dependent finite rectangular array",
                ArrayAll(Seq(ArrayType, Colon, Id("Type"))),
                "The IndexedChain data retain every original d_j,A_j,U_j,V_j and both equalities A_j=U_jV_j and A_(j+1)=V_jU_j. An array has row(j):NumberedRow(A_j,l) for j:Fin(L+1), step(j):G34Step(A_j,A_(j+1),U_j,V_j,leftFactor(j),rightFactor(j),row(j)) for j:Fin L, and nextRow(j):step(j).next=row(j+1). Thus its a_i^j,u_i^j,v_i^j use literal i<l,j<L. Taking l=L gives exactly the source G34 square; intermediate dimensions may vary or vanish.", DescribeRole.Definition),
            Item("generateG34", "Generate the same array from the top and right sides",
                ArrayAll(Seq(Call("generateG34", Id("data"), Id("l"), Id("b"), Id("rin"), Id("r"), Id("hr")), Colon, Call("PrescribedG34Array", Id("data"), Id("l"), Id("b"), Id("rin"), Id("r"))), B("b", Quant(Call("Fin", Call("dimension", Id("data"), Id("j"))), B("j", Call("Fin", Call("successor", Id("L")))))), B("rin", Quant(Call("At", Call("U", Id("data"), Id("j")), Call("b", Call("castSucc", Id("j"))), Call("b", Call("succ", Id("j")))), B("j", Call("Fin", Id("L"))))), B("r", Call("NumberedRow", Call("A", Id("data"), Num(0)), Id("l"))), B("hr", Equal(Call("lastVertex", Id("r")), Call("b", Num(0))))),
                "Here b(j):Fin(d_j) is the actual right-side vertex at each level, rin(j):At(U_j,b(j),b(j+1)) is each supplied right U edge, and r is the supplied A_0 top row with r.vertex(l)=b(0). PrescribedG34Array is the subtype of arrays g satisfying g.row(0)=r, g.row(j).vertex(l)=b(j) at every level and HEq(step(j).u(l),rin(j)) at every step. The recursion generates one complete row, then the actual remaining source layers. It imposes no inhabitance, positivity or commutativity premise.", DescribeRole.Definition),
            Item("g34Step_unique", "Uniqueness of one literal recurrence row",
                StepAll(Seq(Equal(Call("lastVertex", Call("next", Id("p"))), Call("lastVertex", Call("next", Id("q")))), Land, Call("HEq", Call("lastU", Id("p")), Call("lastU", Id("q"))), Implies, Sp, Equal(Id("p"), Id("q"))), B("p", StepType), B("q", StepType)),
                "For two legal G34 steps on the same original A,B,U,V,hA,hB and top row r, equality of their final next vertices and equality of their prescribed last U edges force equality of the entire steps. Theta determines every interior next vertex and half-edge; eta then determines every next numbered edge. HEq records the necessary dependent endpoint transport.", DescribeRole.Theorem),
            Item("g34Array_unique", "Recurrence uniqueness for the entire same array",
                ArrayAll(Seq(Equal(Call("row", Id("p"), Num(0)), Call("row", Id("q"), Num(0))), Land, Call("SameRightVertices", Id("p"), Id("q")), Land, Call("SameRightUEdges", Id("p"), Id("q")), Implies, Sp, Equal(Id("p"), Id("q"))), B("p", ArrayType), B("q", ArrayType)),
                "SameRightVertices means p.row(j).vertex(l)=q.row(j).vertex(l) for every j:Fin(L+1). SameRightUEdges means HEq(p.step(j).u(l),q.step(j).u(l)) for every j:Fin L. With the same top row these data determine equality of all rows, half-edges, actual numbered edges and recurrence proofs by finite level induction. No commutation hypothesis is used.", DescribeRole.Theorem),
            Item("rowWord", "The complete word in a finite numbered row",
                RowAll(Seq(Call("rowWord", Id("A"), Id("l"), Id("r")), Colon, Call("Word", Id("A"), Id("l"), Call("vertex", Id("r"), Num(0)), Call("lastVertex", Id("r")))), B("r", Call("NumberedRow", Id("A"), Id("l")))),
                "Read edges in increasing i order, retaining each intervening vertex, group label and copy number. The zero-length result is the named nil path at r.vertex(0), which is also the final vertex.", DescribeRole.Definition),
            Item("arrayTail", "The actual subarray after the first layer",
                ArraySuccAll(Seq(Call("arrayTail", Id("g")), Colon, Call("G34Array", Call("tail", Id("data")), Id("l"))), B("g", ArrayType)),
                "For data of length L+1, remove the first source layer. The resulting row(j),step(j),nextRow(j) are the original row(j+1),step(j+1),nextRow(j+1). Its source is exactly tail(data), not another chain with equal endpoint products.", DescribeRole.Definition),
            Item("arrayLeftPath", "The source-indexed left U boundary",
                ArrayAll(Seq(Call("arrayLeftPath", Id("g")), Colon, Call("FactorPath", Call("forwardFactors", Call("toChain", Id("data"))), Call("vertex", Call("row", Id("g"), Num(0)), Num(0)), Call("vertex", Call("row", Id("g"), Id("L")), Num(0)))), B("g", ArrayType)),
                "This is the actual factor path (u_0^0,u_0^1,...,u_0^(L−1)), with each edge transported through nextRow to the matching next source row. Its initial endpoint is a_0^0 source and its final endpoint is a_0^L source. At L=0 it is the named nil path.", DescribeRole.Definition),
            Item("arrayOutput", "The actual R output and bottom row",
                ArrayAll(Seq(Call("arrayOutput", Id("g")), Colon, Call("LeftBoundaryAndBottomWord", Id("data"), Id("l"), Id("g"))), B("g", ArrayType)),
                "LeftBoundaryAndBottomWord is the sigma over y:Fin(d_L) of FactorPath(forwardFactors(toChain(data)),row(0).vertex(0),y) times Word(A_L,l,y,row(L).vertex(l)). The constructor uses exactly y=row(L).vertex(0), the literal leftPath, and rowWord of the same array’s bottom row.", DescribeRole.Definition),
            Item("g34_layerSweep", "The sweep evaluates the literal same row",
                LocalRowAll(Equal(Call("layerSweep", Id("U"), Id("V"), Id("l"), Call("firstVertex", Id("r")), Call("lastVertex", Call("next", Id("p"))), Call("topWordAndLastU", Id("r"), Id("p"))), Call("firstUAndBottomWord", Id("p"))), B("p", Call("G34FactorStep", Id("U"), Id("V"), Id("r")))),
                "G34FactorStep(U,V,r) is G34Step(UV,VU,U,V,rfl,rfl,r). The input is the sigma tuple (r.vertex(l),rowWord(UV,l,r),p.u(l)). The output is (p.next.vertex(0),p.u(0),rowWord(VU,l,p.next)). Thus the actual layerSweep evaluates this same legal G34 row, including its prescribed last U edge and every independent label and copy number. The proof recursively evaluates the right suffix and then its remaining local cell.", DescribeRole.Theorem),
            Item("rowTail", "Remove the first actual word edge",
                RowAll(Seq(Call("rowTail", Id("r")), Colon, Call("NumberedRow", Id("A"), Id("l"))),
                    B("r", Call("NumberedRow", Id("A"), Call("successor", Id("l"))))),
                "For r of length l+1, vertex(i)=r.vertex(i.succ) and edge(i)=r.edge(i.succ). This preserves the full actual endpoints and numbered edges.", DescribeRole.Definition),
            Item("stepTail", "Remove the first column of the same typed step",
                Group(Quant(Seq(Call("stepTail", Id("p")), Colon, Call("G34Step", Id("A"), Id("B"), Id("U"), Id("V"), Id("hA"), Id("hB"), Call("rowTail", Id("r")))),
                    B("n", Id("Nat")), B("k", Id("Nat")), B("l", Id("Nat")),
                    B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))), B("B", Call("GroupMat", Id("H"), Id("k"), Id("k"))),
                    B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))), B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))),
                    B("hA", Equal(Id("A"), Multiply(Id("U"), Id("V")))), B("hB", Equal(Id("B"), Multiply(Id("V"), Id("U")))),
                    B("r", Call("NumberedRow", Id("A"), Call("successor", Id("l")))),
                    B("p", Call("G34Step", Id("A"), Id("B"), Id("U"), Id("V"), Id("hA"), Id("hB"), Id("r")))), true),
                "The next row is rowTail(p.next). All u,v,theta,eta fields are restricted by i.succ. Both matrix equations remain the original hA,hB.", DescribeRole.Definition),
            Item("rowPrefix", "Remove the last actual word edge",
                RowAll(Seq(Call("rowPrefix", Id("r")), Colon, Call("NumberedRow", Id("A"), Id("l"))),
                    B("r", Call("NumberedRow", Id("A"), Call("successor", Id("l"))))),
                "For r of length l+1, vertex(i)=r.vertex(i.castSucc) and edge(i)=r.edge(i.castSucc), retaining every prefix endpoint and numbered edge.", DescribeRole.Definition),
            Item("arrayPrefix", "Remove the last column of every actual row",
                ArrayAll(Seq(Call("arrayPrefix", Id("g")), Colon, Call("G34Array", Id("data"), Id("l"))),
                    B("g", Call("G34Array", Id("data"), Call("successor", Id("l"))))),
                "All rows use rowPrefix, all steps restrict their u,v,theta,eta fields by castSucc, and every nextRow proof is transported by rowPrefix. The original full indexed chain and both factor equations are unchanged.", DescribeRole.Definition))));
}
