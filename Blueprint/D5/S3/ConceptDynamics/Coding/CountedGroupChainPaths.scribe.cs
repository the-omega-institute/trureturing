using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGroupChainPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.";
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
        "Complete original long compatibility equations. All numbered edges, ordered labels and source conditions are retained.",
        H("Complete original long compatibility equations"),
        Blocks(
            Item("rightBoundaryPath", "Reassemble every prescribed original U edge",
                BoundaryAll(Seq(Call("rightBoundaryPath", Id("data"), Id("v"), Id("e")), Colon,
                    Call("FactorPath", Call("forwardFactors", Call("toChain", Id("data"))), Call("v", Num(0)), Call("v", Id("L")))),
                    B("v", Call("BoundaryVertices", Id("data"))), B("e", Call("BoundaryUEdges", Id("data"), Id("v")))),
                "BoundaryVertices means v(k):Fin(d_k) for every k:Fin(L+1). BoundaryUEdges means e(k):At(U_k,v(k),v(k+1)) for every k:Fin L. Reassembly reads these edges in increasing source-layer order; the nil case retains v(0). The generated-boundary bridge proves that unpacking and reassembling the original factor path recovers that path, including labels and copies.", DescribeRole.Definition),
            Item("wordFactorArray_right", "The entire generated right boundary is the original input",
                ArrayAll(Call("HEq", Call("arrayRightPath", Call("wordFactorArray", Id("data"), Id("l"), Id("i"), Id("j"), Id("p"))), Call("inputRightPath", Id("p"))),
                    B("i", Call("Fin", Call("dimension", Id("data"), Num(0)))), B("j", Call("Fin", Call("dimension", Id("data"), Id("L")))), B("p", Call("OriginalWordAndRightFactorPath", Id("data"), Id("l"), Id("i"), Id("j")))),
                "For all original typed inputs p, arrayRightPath(wordFactorArray(data,l,i,j,p)) is heterogeneously equal to p.second.second. Every generated last U edge is the actual prescribed input edge; finite induction reassembles the complete original path. Together with wordFactorArray_top and its endpoint identities, this gives the actual Word/FactorPath-to-G34 bridge for every input, including a named nil word and path.", DescribeRole.Theorem),
            Item("phiRPower_long", "The original long R law for every supplied chain", LongLaw(false, false),
                "For all original H,n,m,L,A,B,c,i,x,y,j and paths r:forwardFactors(c)(i,y),s:backwardFactors(c)(y,x),rprime:forwardFactors(c)(x,j), the displayed equality holds on the entire typed input. The actual chain is indexed without changing its factors; its Word/FactorPath input generates the prescribed G34 square. The two recovered triangle boundaries identify exactly r,s,rprime. The equation is a conclusion, with no long-law, commutation or enumeration hypothesis.", DescribeRole.Theorem),
            Item("phiSPower_long", "The original long S law on that same tuple", LongLaw(true, false),
                "In this dual displayed formula r names the S path, s names the R path and rprime names the second S path. The proof applies the constructed R law to reverseChain(c), whose U factors are the original V factors in decreasing order. Reversing twice recovers c, so its terminal triangle is the original psi0. The result uses the same A,B,R,S,L and all actual numbered paths; it restricts neither the group nor dimensions.", DescribeRole.Theorem),
            Item("matrixPhiRPower", "Synchronous whole-rank conjugation of the complete R sweep",
                OrderedChainAll(MapType("matrixPhiRPower", SweepIn(false, true, Id("l")), SweepOut(false, true, Id("l")), Id("c"), Id("l"), Id("i"), Id("j")), [B("l", Id("Nat")), .. MapEndpoints()]),
                "At the incoming and outgoing R boundary use exactly pathAtEquiv(forwardFactors(c)) and its inverse, preserving the whole-factor lexicographic rank. The intervening map is the literal complete phiRPower, the right-to-left iteration of the original one-edge phiR. Intermediate rank transports cancel when composing columns. No new enumeration or endpoint matrix is introduced.", DescribeRole.Definition),
            Item("matrixPhiSPower", "Synchronous whole-rank conjugation of the complete S sweep",
                OrderedChainAll(MapType("matrixPhiSPower", SweepIn(true, true, Id("l")), SweepOut(true, true, Id("l")), Id("c"), Id("l"), Id("i"), Id("j")), [B("l", Id("Nat")), .. MapEndpoints(true)]),
                "Use the identical pathAtEquiv(backwardFactors(c)) rank in every S occurrence before and after the literal reversed-chain phiSPower. The complete word and its endpoints are unchanged. This is the dual synchronous conjugation of the same actual supplied chain.", DescribeRole.Definition),
            Item("matrixPhiRPower_long", "The original matrix-edge R compatibility equation", LongLaw(false, true),
                "Every r,rprime is an actual At(R(c)) edge and s an actual At(S(c)) edge. All occurrences in matrixPsi0,matrixPsiL and matrixPhiRPower use the same whole-fiber ranks. Apply the actual path-level long law and cancel the outgoing rank roundtrip; every independent edge number and label is preserved.", DescribeRole.Theorem),
            Item("matrixPhiSPower_long", "The original matrix-edge S compatibility equation", LongLaw(true, true),
                "The dual law uses the same concrete cumulative R(c),S(c), source A, target B and original length L. In this displayed formula r and rprime are At(S(c)) edges and s is At(R(c)). It follows from the path-level dual law through the exact same S rank; no separately chosen compatible tuple occurs.", DescribeRole.Theorem),
            Item("Compatibility", "Both long laws at the original concrete tuple",
                OrderedChainAll(Seq(Call("Compatibility", Id("c")), Colon, Id("Prop"))),
                "The certificate asserts AR=RB,BS=SA,RS=A^L,SR=B^L and both fully quantified matrix-edge long equations just displayed, with R=R(c),S=S(c) and the four actual equivalences matrixPsi0,matrixPsiL,matrixPhiR,matrixPhiS. Each equivalence supplies both inverse identities. The complete-word sweeps are their synchronous whole-rank conjugations. The certificate has no supplied-law fields or replacement endpoints.", DescribeRole.Definition),
            Item("original27_2", "The complete same-tuple source compatibility certificate",
                OrderedChainAll(Call("Compatibility", Id("c"))),
                "For every finite ordered group and every actual natural group-ring chain c:Chain(H,A,B,L), construct Compatibility(c). Its four algebraic equations are the cumulative equations of that chain. Both long laws are proved for every typed endpoint and every numbered input by the literal G34 construction and its reverse, using the same whole-fiber R/S ranks. Zero length, empty coefficient fibers and varying or zero dimensions remain in the universal telescope.", DescribeRole.Theorem))));
}
