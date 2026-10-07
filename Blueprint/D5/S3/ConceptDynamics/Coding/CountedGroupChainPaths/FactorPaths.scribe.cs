using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGroupChainPathsFactorPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.";
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
    private static Formula SnocAll(Formula body) => Group(Quant(body,
        B("n", Id("Nat")), B("k", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
        B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
        B("B", Call("GroupMat", Id("H"), Id("k"), Id("k"))),
        B("C", Call("GroupMat", Id("H"), Id("m"), Id("m"))),
        B("c", Call("Chain", Id("H"), Id("A"), Id("B"), Id("L"))),
        B("U", Call("GroupMat", Id("H"), Id("k"), Id("m"))),
        B("V", Call("GroupMat", Id("H"), Id("m"), Id("k"))),
        B("hB", Equal(Id("B"), Multiply(Id("U"), Id("V")))),
        B("hC", Equal(Id("C"), Multiply(Id("V"), Id("U"))))));
    private static Formula Snoc => Call("chainSnoc", Id("c"), Id("U"), Id("V"), Id("hB"), Id("hC"));
public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ordered factor paths and reversible peeling. All numbered edges, ordered labels and source conditions are retained.",
        H("Actual ordered factor paths and reversible peeling"),
        Blocks(
            Item("Factors", "The ordered list of actual rectangular factors",
                Group(Quant(Seq(Call("Factors", Id("H"), Id("n"), Id("m"), Id("L")), Colon, Id("Type")),
                    B("n", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat"))), finite: false),
                "Factors H n m L stores L actual natural group-ring matrices with composable finite dimensions, beginning at n and ending at m. The zero-length constructor has the same initial and terminal dimension. A cons constructor stores its first rectangular matrix and the entire remaining sequence; dimensions may vary and may be zero.",
                DescribeRole.Definition),
            Item("factorProduct", "Multiply in the prescribed factor order",
                FactorsAll(Seq(Product, Colon, Call("GroupMat", Id("H"), Id("n"), Id("m")))),
                "The product of the empty sequence is the identity matrix. The product of a sequence with first matrix M and tail f is M times factorProduct(f). Thus the recursive multiplication follows the left-to-right order of all supplied factors.",
                DescribeRole.Definition),
            Item("factorSnoc", "Retain a last factor",
                FactorsAll(Seq(Call("factorSnoc", Id("f"), Id("M")), Colon,
                    Call("Factors", Id("H"), Id("n"), Id("k"),
                        Call("successor", Id("L")))), false, false,
                    B("k", Id("Nat")),
                    B("M", Call("GroupMat", Id("H"), Id("m"), Id("k")))),
                "factorSnoc f M appends the actual rectangular matrix M at the right-hand end. Its product is factorProduct(f) times M. This operation expresses the decreasing order of the V factors without changing any factor data.",
                DescribeRole.Definition),
            Item("FactorPath", "Typed paths with a named empty vertex",
                FactorsAll(Seq(Path, Colon, Id("Type")), false, false, Endpoints),
                "FactorPath f i j retains the complete ordered factor tuple between endpoints i and j. At length zero it contains a vertex v with v=i and v=j. At a nonempty layer it contains the next vertex v, a group label h, a number in Fin(coeff(M[i,v],h)), and a path in the tail from v to j. The nested sigma and product orders compare these coordinates lexicographically. No edge number is identified with another.",
                DescribeRole.Definition),
            Item("factorLabel", "Ordered total label",
                FactorsAll(Seq(Call("factorLabel", Id("f"), Id("p")), Colon, Id("H")), false, false,
                    [.. Endpoints, B("p", Path)]),
                "The empty path has label one. A nonempty path has label h times the tail label, where h is the first edge label. This is the ordered group product in traversal order; no commutativity assumption is used.",
                DescribeRole.Definition),
            Item("nilPath", "The specified zero-edge vertex",
                Group(Quant(Seq(Call("nilPath", Id("i")), Colon,
                    Call("FactorPath", Call("nil", Id("H"), Id("n")), Id("i"), Id("i"))),
                    B("n", Id("Nat")), B("i", Call("Fin", Id("n")))), finite: false),
                "nilPath i stores the actual vertex i and both endpoint equalities. Its total label is one. At a zero-dimensional carrier there is no vertex to choose, and no extra inhabitance assumption is imposed.",
                DescribeRole.Definition),
            Item("consPath", "The actual first numbered edge",
                Group(Quant(Seq(Call("consPath", Id("M"), Id("f"), Id("e"), Id("p")), Colon,
                    Call("FactorPath", Call("cons", Id("M"), Id("f")),
                        Call("source", Id("e")), Id("j"))),
                    B("n", Id("Nat")), B("k", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
                    B("M", Call("GroupMat", Id("H"), Id("n"), Id("k"))),
                    B("f", Call("Factors", Id("H"), Id("k"), Id("m"), Id("L"))),
                    B("e", Call("Edge", Id("M"))), B("j", Call("Fin", Id("m"))),
                    B("p", Call("FactorPath", Id("f"), Call("target", Id("e")), Id("j")))), finite: false),
                "consPath stores the first edge's target, group label and copy number and the supplied typed tail. Its outside source is exactly the edge source, and the tail begins at exactly the edge target.",
                DescribeRole.Definition),
            Item("FactorFiber", "The entire endpoint and label fiber",
                FactorsAll(Equal(Fiber, Call("Subtype", Path,
                    Call("labelEquals", Id("f"), Id("g")))), false, false, EndpointsLabel),
                "The fiber contains all actual paths with the specified endpoints and total ordered group label. It includes every original coefficient number. A fiber may be empty.",
                DescribeRole.Definition),
            Item("fiberConsEquiv", "Resolve the first factor of a whole fiber",
                Group(Quant(Call("Equiv", Call("FactorFiber", Call("cons", Id("M"), Id("f")),
                        Id("i"), Id("j"), Id("g")),
                    Call("FirstFactorFiber", Id("M"), Id("f"), Id("i"), Id("j"), Id("g"))),
                    B("n", Id("Nat")), B("k", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
                    B("M", Call("GroupMat", Id("H"), Id("n"), Id("k"))),
                    B("f", Call("Factors", Id("H"), Id("k"), Id("m"), Id("L"))),
                    B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("m"))), B("g", Id("H"))), finite: false),
                "FirstFactorFiber is the sigma over v in Fin k and h in H of Fin(coeff(M[i,v],h)) times FactorFiber(f,v,j,h inverse times g). The equivalence retains the same first vertex, label, number and actual tail. The equation h times label(tail)=g is equivalent to label(tail)=h inverse times g.",
                DescribeRole.Definition),
            Item("fiber_card", "Coefficients count complete actual paths",
                FactorsAll(Equal(Call("card", Fiber),
                    Call("coeff", Call("entry", Product, Id("i"), Id("j")), Id("g"))),
                    false, true, EndpointsLabel),
                "Induction on the factor sequence reduces the count to the sum over the next vertex and first group label. Each summand is the first coefficient times the count of the actual tail fiber. Group-ring convolution and rectangular matrix multiplication give precisely the product coefficient. At length zero the only possible path has identical endpoints and label one; every other fiber is empty.",
                DescribeRole.Theorem),
            Item("rankedFiberOrderIso", "The increasing global rank",
                FactorsAll(Call("OrderIso", Copies, Fiber), true, true, EndpointsLabel),
                "The increasing finite-order enumeration ranks the complete endpoint and total-label fiber in one operation. Its order is the lexicographic order of every original factor-edge coordinate. Empty fibers have a unique empty order isomorphism. This enumeration does not identify an iterated binary rank with the whole-path rank.",
                DescribeRole.Definition),
            Item("rankedFiberEquiv", "Both directions of the global fiber rank",
                FactorsAll(Call("Equiv", Copies, Fiber), true, true, EndpointsLabel),
                "The equivalence underlying the increasing rank sends copy c of the cumulative matrix edge to the c-th complete factor tuple. The inverse returns that same global rank and recovers all factor-edge data.",
                DescribeRole.Definition),
            Item("edgePathEquiv", "Transport all standard matrix edges",
                FactorsAll(Call("Equiv", Call("Edge", Product),
                    Call("AllEndpointLabelFibers", Id("f"))), true),
                "AllEndpointLabelFibers is the sigma over i in Fin n, j in Fin m and g in H of FactorFiber(f,i,j,g). The equivalence first reads the standard edge's source, target, label and copy number, then applies the global rank in that same fiber. Both outside endpoints and the total ordered label are therefore preserved, and both inverse laws recover every original copy number.",
                DescribeRole.Definition),
            Item("Chain", "Prescribed factor equalities at every layer",
                Group(Quant(Seq(Call("Chain", Id("H"), Id("A"), Id("B"), Id("L")), Colon, Id("Type")),
                    B("n", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
                    B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
                    B("B", Call("GroupMat", Id("H"), Id("m"), Id("m"))))),
                "Chain H A B L stores the actual length-L supplied chain in Type. A cons step retains U, V, its source matrix A, its next matrix C, the equalities A=UV and C=VU, and the entire tail. The nil step retains its matrix and has identical endpoints. The data impose neither positive dimensions nor positive coefficients.",
                DescribeRole.Definition),
            Item("forwardFactors", "Increasing U factor order",
                ChainAll(Seq(Call("forwardFactors", Id("c")), Colon, Call("Factors", Id("H"), Id("n"), Id("m"), Id("L")))),
                "forwardFactors keeps U at the first layer and recursively keeps the tail's U factors. Thus it is exactly U0 through U(L-1), with all heterogeneous dimensions retained.",
                DescribeRole.Definition),
            Item("backwardFactors", "Decreasing V factor order",
                ChainAll(Seq(Call("backwardFactors", Id("c")), Colon, Call("Factors", Id("H"), Id("m"), Id("n"), Id("L")))),
                "backwardFactors recursively keeps the tail's reversed V factors and appends the first V at the right. Thus it is exactly V(L-1) through V0.",
                DescribeRole.Definition),
            Item("R", "The forward cumulative rectangle",
                ChainAll(Equal(Call("R", Id("c")),
                    Call("factorProduct", Call("forwardFactors", Id("c"))))),
                "R has size n by m and is the ordered product U0 through U(L-1). The empty chain gives the identity matrix.",
                DescribeRole.Definition),
            Item("S", "The reverse cumulative rectangle",
                ChainAll(Equal(Call("S", Id("c")),
                    Call("factorProduct", Call("backwardFactors", Id("c"))))),
                "S has size m by n and is the ordered product V(L-1) through V0. The empty chain gives the identity matrix.",
                DescribeRole.Definition),
            Item("cumulative_equations", "The four equations for the same chain",
                ChainAll(And(Equal(Call("product", Id("A"), Call("R", Id("c"))),
                    Call("product", Call("R", Id("c")), Id("B"))),
                    And(Equal(Call("product", Id("B"), Call("S", Id("c"))),
                        Call("product", Call("S", Id("c")), Id("A"))),
                        And(Equal(Call("product", Call("R", Id("c")), Call("S", Id("c"))),
                            Call("power", Id("A"), Id("L"))),
                            Equal(Call("product", Call("S", Id("c")), Call("R", Id("c"))),
                                Call("power", Id("B"), Id("L"))))))),
                "The two intertwining equations pass the source matrix through every factor using matrix associativity. For RS, induction gives U times the next matrix to the tail length times V; the rectangular exchange-power identity makes this A to the full length. For SR, the tail intertwining equation gives the terminal power. All four equations concern these same R and S. Length one reduces to the supplied U and V, and length zero reduces to the identity matrices.",
                DescribeRole.Theorem),
            Item("IndexedChain", "The complete indexed source telescope",
                Group(Quant(Seq(Call("IndexedChain", Id("H"), Id("L")), Colon, Id("Type")),
                    B("L", Id("Nat")))),
                "The indexed data have dimensions d(j) for j in Fin(L+1), matrices A(j) of size d(j) by d(j), U(j) of size d(j) by d(j+1), and V(j) of the opposite size for j in Fin L. They include both A(j)=U(j)V(j) and A(j+1)=V(j)U(j) for every layer. All original factors are supplied data.",
                DescribeRole.Definition),
            Item("tail", "The actual shifted indexed chain",
                Group(Quant(Seq(Call("tail", Id("c")), Colon, Call("IndexedChain", Id("H"), Id("L"))),
                    B("L", Id("Nat")),
                    B("c", Call("IndexedChain", Id("H"), Call("successor", Id("L")))))),
                "The tail replaces every layer j by j+1 in d, A, U and V and retains the corresponding original factor equalities.",
                DescribeRole.Definition),
            Item("toChain", "Recursion retains the prescribed indexed data",
                Group(Quant(Seq(Call("toChain", Id("c")), Colon,
                    Call("Chain", Id("H"), Call("A", Id("c"), D(0)),
                        Call("A", Id("c"), Call("last", Id("L"))), Id("L"))),
                    B("L", Id("Nat")), B("c", Call("IndexedChain", Id("H"), Id("L"))))),
                "toChain starts with the actual U(0), V(0) and their two given equalities and then recurses on the indexed tail. Its source is A(0), its terminal matrix is A(L), and its length is L. It never selects another chain with the same endpoints." ,
                DescribeRole.Definition),
            Item("At", "Numbered edges at fixed endpoints",
                Group(Quant(Seq(Call("At", Id("M"), Id("i"), Id("j")), Colon, Sig("g", Id("H"), Call("Fin", Call("coeff", Call("entry", Id("M"), Id("i"), Id("j")), Id("g"))))), [ B("n", Id("Nat")), B("m", Id("Nat")), B("M", Call("GroupMat", Id("H"), Id("n"), Id("m"))), .. Endpoints]), finite: false),
                "At M i j contains the group label g and the independent copy number c in Fin(coeff(M[i,j],g)). The endpoints are fixed by its type.", DescribeRole.Definition),
            Item("orderedAtEquiv", "The prescribed theta and eta ranks",
                Group(Quant(MapType("orderedAtEquiv", At(Call("product", Id("U"), Id("V")), "i", "j"), Sig("v", Call("Fin", Id("k")), Pair(At(Id("U"), "i", "v"), At(Id("V"), "v", "j"))), Id("U"), Id("V"), Id("i"), Id("j")), B("n", Id("Nat")), B("k", Id("Nat")), B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))), B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("n")))), true),
                "The map uses orderedFiberEquiv with exactly the prescribed order: middle vertex, first group label, first copy, second copy. The second label is first-label inverse times total label. The inverse multiplies the labels in this order and returns the rank in the same local fiber. Empty fibers require no representative.", DescribeRole.Definition),
            Item("wordFactors", "Repeated actual square matrix",
                Group(Quant(Seq(Call("wordFactors", Id("A"), Id("l")), Colon, Call("Factors", Id("H"), Id("n"), Id("n"), Id("l"))), B("n", Id("Nat")), B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))), B("l", Id("Nat"))), finite: false),
                "wordFactors A l stores l copies of the actual A matrix. Length zero is the nil factor sequence, and each successor prepends A.", DescribeRole.Definition),
            Item("Word", "Finite actual A words",
                Group(Quant(Equal(W("A", Id("l"), "i", "j"), Call("FactorPath", Call("wordFactors", Id("A"), Id("l")), Id("i"), Id("j"))), B("n", Id("Nat")), B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))), B("l", Id("Nat")), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("n")))), finite: false),
                "Words retain their endpoints and every ordered label and copy number. A zero-edge word retains its specified vertex.", DescribeRole.Definition),
            Item("pathHeadEquiv", "Read and restore the first factor edge",
                Group(Quant(MapType("pathHeadEquiv", Call("FactorPath", Call("cons", Id("M"), Id("f")), Id("i"), Id("j")), Sig("v", Call("Fin", Id("k")), Pair(At(Id("M"), "i", "v"), Call("FactorPath", Id("f"), Id("v"), Id("j")))), Id("M"), Id("f"), Id("i"), Id("j")), [ B("n", Id("Nat")), B("k", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")), B("M", Call("GroupMat", Id("H"), Id("n"), Id("k"))), B("f", Call("Factors", Id("H"), Id("k"), Id("m"), Id("L"))), .. Endpoints]), finite: false),
                "The first numbered edge and the complete tail are unpacked and repacked without changing their data. The two composites are identities.", DescribeRole.Definition),
            Item("rightNilEquiv", "Read an edge followed by its named nil",
                Group(Quant(MapType("rightNilEquiv", Sig("v", Call("Fin", Id("m")), Pair(At(Id("M"), "i", "v"), Call("FactorPath", Call("nil", Id("H"), Id("m")), Id("v"), Id("j")))), At(Id("M"), "i", "j"), Id("M"), Id("i"), Id("j")), [ B("n", Id("Nat")), B("m", Id("Nat")), B("M", Call("GroupMat", Id("H"), Id("n"), Id("m"))), .. Endpoints]), finite: false),
                "The nil endpoint equalities identify v with j. The inverse appends the actual nilPath j, and both composites recover the edge and named vertex.", DescribeRole.Definition),
            Item("pathSnocEquiv", "Split off the last actual numbered edge",
                Group(Quant(MapType("pathSnocEquiv", Call("FactorPath", Call("factorSnoc", Id("f"), Id("M")), Id("i"), Id("j")), Sig("v", Call("Fin", Id("k")), Pair(Call("FactorPath", Id("f"), Id("i"), Id("v")), At(Id("M"), "v", "j"))), Id("f"), Id("M"), Id("i"), Id("j")), [ B("n", Id("Nat")), B("k", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")), B("f", Call("Factors", Id("H"), Id("n"), Id("k"), Id("L"))), B("M", Call("GroupMat", Id("H"), Id("k"), Id("m"))), .. Endpoints]), finite: false),
                "Structural recursion separates the final actual edge from the entire preceding path. Its inverse appends that same edge. It preserves all preceding copies, the last copy, the outside endpoints and the ordered product.", DescribeRole.Definition),
            Item("ChainBoundary", "The actual increasing and decreasing factor paths",
                UnorderedChainAll(Equal(Call("ChainBoundary", Id("c"), Id("i"), Id("j")), CB()), MapEndpoints(square: true)),
                "The sigma vertex is the common middle endpoint. The first path is the increasing U sequence and the second path is the decreasing V sequence of the same supplied chain.", DescribeRole.Definition),
            Item("psi0", "The source triangle",
                OrderedChainAll(MapType("psi0", CB(false), W("A", Id("L"), "i", "j"), Id("c"), Id("i"), Id("j")), MapEndpoints(false, true)),
                "The inverse peels each theta row, saves its first U edge and last V edge, and joins internal adjacent VU pairs by eta. Its forward algorithm reverses these operations from the named nil word. Both composites are identities on all typed inputs, including length zero and empty coefficient fibers. No dimension is required to be positive.", DescribeRole.Definition),
            Item("psiL", "The terminal triangle",
                OrderedChainAll(MapType("psiL", CB(true), W("B", Id("L"), "i", "j"), Id("c"), Id("i"), Id("j")), MapEndpoints(true, true)),
                "The actual reversed chain exchanges U and V and reverses the layer order. Applying the source triangle to it defines the terminal triangle, using eta to split and theta to rejoin. Both composites are identities on all typed inputs, including length zero and empty coefficient fibers. No dimension is required to be positive.", DescribeRole.Definition),
            Item("matrixPsi0", "The source triangle on matrix edges",
                OrderedChainAll(MapType("matrixPsi0", Sig("v", Call("Fin", Id("m")), Pair(At(Call("R", Id("c")), "i", "v"), At(Call("S", Id("c")), "v", "j"))), W("A", Id("L"), "i", "j"), Id("c"), Id("i"), Id("j")), MapEndpoints(false, true)),
                "Every R and S occurrence is transported by pathAtEquiv using the single increasing whole-factor fiber rank. The inverse peels each theta row, saves its first U edge and last V edge, and joins internal adjacent VU pairs by eta. Its forward algorithm reverses these operations from the named nil word. Both composites are identities on all typed inputs, including length zero and empty coefficient fibers. No dimension is required to be positive.", DescribeRole.Definition),
            Item("matrixPsiL", "The terminal triangle on matrix edges",
                OrderedChainAll(MapType("matrixPsiL", Sig("v", Call("Fin", Id("n")), Pair(At(Call("S", Id("c")), "i", "v"), At(Call("R", Id("c")), "v", "j"))), W("B", Id("L"), "i", "j"), Id("c"), Id("i"), Id("j")), MapEndpoints(true, true)),
                "Every R and S occurrence is transported by pathAtEquiv using the single increasing whole-factor fiber rank. The actual reversed chain exchanges U and V and reverses the layer order. Applying the source triangle to it defines the terminal triangle, using eta to split and theta to rejoin. Both composites are identities on all typed inputs, including length zero and empty coefficient fibers. No dimension is required to be positive.", DescribeRole.Definition),
            Item("phiR", "The phiR actual sweep",
                OrderedChainAll(MapType("phiR", SweepIn(false, false), SweepOut(false, false), Id("c"), Id("i"), Id("j")), MapEndpoints(false)),
                "The sweep splits theta, saves the U edge, joins eta with the incoming U edge and continues through the original layers. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.", DescribeRole.Definition),
            Item("phiS", "The phiS actual sweep",
                OrderedChainAll(MapType("phiS", SweepIn(true, false), SweepOut(true, false), Id("c"), Id("i"), Id("j")), MapEndpoints(true)),
                "The sweep uses the actual reversed chain and its decreasing original V factors. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.", DescribeRole.Definition),
            Item("matrixPhiR", "The matrixPhiR actual sweep",
                OrderedChainAll(MapType("matrixPhiR", SweepIn(false, true), SweepOut(false, true), Id("c"), Id("i"), Id("j")), MapEndpoints(false)),
                "Both occurrences of the cumulative matrix edge use the same whole-factor rank. The sweep splits theta, saves the U edge, joins eta with the incoming U edge and continues through the original layers. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.", DescribeRole.Definition),
            Item("matrixPhiS", "The matrixPhiS actual sweep",
                OrderedChainAll(MapType("matrixPhiS", SweepIn(true, true), SweepOut(true, true), Id("c"), Id("i"), Id("j")), MapEndpoints(true)),
                "Both occurrences of the cumulative matrix edge use the same whole-factor rank. The sweep uses the actual reversed chain and its decreasing original V factors. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.", DescribeRole.Definition),
            Item("phiRPower", "The phiRPower actual sweep",
                OrderedChainAll(MapType("phiRPower", SweepIn(false, false, length: Id("l")), SweepOut(false, false, length: Id("l")), Id("c"), Id("l"), Id("i"), Id("j")), [ B("l", Id("Nat")), .. MapEndpoints(false)]),
                "Each finite word is processed from its rightmost column to its leftmost column. The sweep splits theta, saves the U edge, joins eta with the incoming U edge and continues through the original layers. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.", DescribeRole.Definition),
            Item("phiSPower", "The phiSPower actual sweep",
                OrderedChainAll(MapType("phiSPower", SweepIn(true, false, length: Id("l")), SweepOut(true, false, length: Id("l")), Id("c"), Id("l"), Id("i"), Id("j")), [ B("l", Id("Nat")), .. MapEndpoints(true)]),
                "Each finite word is processed from its rightmost column to its leftmost column. The sweep uses the actual reversed chain and its decreasing original V factors. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.", DescribeRole.Definition),
            Item("reverseChain", "The actual chain in decreasing layer order",
                UnorderedChainAll(Seq(Call("reverseChain", Id("c")), Colon, Call("Chain", Id("H"), Id("B"), Id("A"), Id("L")))),
                "The reversed chain retains each original matrix and factor equality, exchanging U and V and visiting the original layers in decreasing order. Its forward factors are precisely the original backward factors, and its backward factors are precisely the original forward factors.", DescribeRole.Definition),
            Item("chainSnoc", "Append the prescribed final SSE step",
                Group(Quant(Seq(Call("chainSnoc", Id("c"), Id("U"), Id("V"), Id("hB"), Id("hC")), Colon, Call("Chain", Id("H"), Id("A"), Id("C"), Call("successor", Id("L")))), B("n", Id("Nat")), B("k", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")), B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))), B("B", Call("GroupMat", Id("H"), Id("k"), Id("k"))), B("C", Call("GroupMat", Id("H"), Id("m"), Id("m"))), B("c", Call("Chain", Id("H"), Id("A"), Id("B"), Id("L"))), B("U", Call("GroupMat", Id("H"), Id("k"), Id("m"))), B("V", Call("GroupMat", Id("H"), Id("m"), Id("k"))), B("hB", Equal(Id("B"), Call("product", Id("U"), Id("V")))), B("hC", Equal(Id("C"), Call("product", Id("V"), Id("U")))))),
                "The operation appends this actual final step after the retained chain. Its U sequence appends U; its decreasing V sequence prepends V.", DescribeRole.Definition),
            Item("pathAtEquiv", "The single whole-factor rank at fixed endpoints",
                FactorsAll(MapType("pathAtEquiv", At(Product, "i", "j"), Path, Id("f"), Id("i"), Id("j")), true, true, Endpoints),
                "The map reads the label and global rank of a cumulative matrix edge and returns the actual complete factor path in that fiber. Its inverse reads the same fiber rank. All original factor copies, endpoints and the ordered total label are recovered.", DescribeRole.Definition),
            Item("PeelBoundary", "The saved U edge, internal VU word and saved V edge",
                Group(Quant(Equal(Call("PeelBoundary", Id("U"), Id("V"), Id("l"), Id("i"), Id("j")), Sig("x", Call("Fin", Id("k")), Sig("y", Call("Fin", Id("k")), Pair(At(Id("U"), "i", "x"), Pair(Call("Word", Call("product", Id("V"), Id("U")), Id("l"), Id("x"), Id("y")), At(Id("V"), "y", "j")))))), B("n", Id("Nat")), B("k", Id("Nat")), B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))), B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))), B("l", Id("Nat")), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("n")))), finite: false),
                "The outside half-edges are retained individually. The internal word has length l, so the original word has length l+1. All middle endpoints are typed and retained.", DescribeRole.Definition),
            Item("peelRow", "One triangular peeling layer",
                Group(Quant(MapType("peelRow", Call("Word", Call("product", Id("U"), Id("V")), Call("successor", Id("l")), Id("i"), Id("j")), Sig("x", Call("Fin", Id("k")), Sig("y", Call("Fin", Id("k")), Pair(At(Id("U"), "i", "x"), Pair(Call("Word", Call("product", Id("V"), Id("U")), Id("l"), Id("x"), Id("y")), At(Id("V"), "y", "j"))))), Id("U"), Id("V"), Id("l"), Id("i"), Id("j")), B("n", Id("Nat")), B("k", Id("Nat")), B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))), B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))), B("l", Id("Nat")), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("n")))), true),
                "Split every theta edge, save the leftmost U and rightmost V, and join adjacent internal VU pairs using eta. The inverse splits those eta edges, restores the saved edges, and joins the theta pairs. Both composites recover every label and independent copy number.", DescribeRole.Definition),
            Item("localSweep", "The actual local theta-eta cell",
                Group(Quant(MapType("localSweep", Sig("x", Call("Fin", Id("n")), Pair(At(Call("product", Id("U"), Id("V")), "i", "x"), At(Id("U"), "x", "j"))), Sig("y", Call("Fin", Id("k")), Pair(At(Id("U"), "i", "y"), At(Call("product", Id("V"), Id("U")), "y", "j"))), Id("U"), Id("V"), Id("i"), Id("j")), B("n", Id("Nat")), B("k", Id("Nat")), B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))), B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("k")))), true),
                "Split the actual theta rank into u,v and return u together with eta(v,u-prime). The inverse splits eta and rejoins theta. All three half-edge labels occur in the same order.", DescribeRole.Definition),
            Item("forward_snoc", "Forward factors of an appended actual step",
                SnocAll(Equal(Call("forwardFactors", Snoc), Call("factorSnoc", Call("forwardFactors", Id("c")), Id("U")))),
                "For the supplied equalities B=UV and C=VU, appending the step retains the increasing factors of c and then U. Dimensions n,k,m and the full original length L are quantified.", DescribeRole.Theorem),
            Item("backward_snoc", "Backward factors of an appended actual step",
                SnocAll(Equal(Call("backwardFactors", Snoc), Call("FactorsCons", Id("V"), Call("backwardFactors", Id("c"))))),
                "The decreasing backward factor list begins with the appended V, followed by every backward factor of c. The same supplied B=UV,C=VU equalities are retained.", DescribeRole.Theorem),
            Item("reverse_forward", "Reversal exchanges the complete forward factor list",
                ChainAll(Equal(Call("forwardFactors", Call("reverseChain", Id("c"))), Call("backwardFactors", Id("c")))),
                "For every actual chain c, the increasing factors of its reversal are exactly the decreasing original backward factors, including the named nil chain.", DescribeRole.Theorem),
            Item("reverse_backward", "Reversal exchanges the complete backward factor list",
                ChainAll(Equal(Call("backwardFactors", Call("reverseChain", Id("c"))), Call("forwardFactors", Id("c")))),
                "For every actual chain c, the decreasing factors of its reversal are exactly the increasing original forward factors.", DescribeRole.Theorem))));
}
