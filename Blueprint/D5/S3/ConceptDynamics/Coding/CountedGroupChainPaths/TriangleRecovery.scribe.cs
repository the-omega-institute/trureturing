using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGroupChainPathsTriangleRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.";
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

    private static Formula RowAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("n", Id("Nat")), B("l", Id("Nat")),
            B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))), .. extra]), finite: false);
    private static Formula PeelingRowAll(Formula body) =>
        Group(Quant(body, B("n", Id("Nat")), B("k", Id("Nat")), B("l", Id("Nat")),
            B("U", Call("GroupMat", Id("H"), Id("n"), Id("k"))),
            B("V", Call("GroupMat", Id("H"), Id("k"), Id("n"))),
            B("r", Call("NumberedRow", Multiply(Id("U"), Id("V")), Call("successor", Id("l")))),
            B("p", Call("G34FactorStep", Id("U"), Id("V"), Id("r")))), true);
    private static Formula ArrayAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("L", Id("Nat")), B("l", Id("Nat")),
            B("data", Call("IndexedChain", Id("H"), Id("L"))), .. extra]), true);
    private static Formula SquareArrayAll(Formula body, params Formula.BoundVariable[] extra) =>
        Group(Quant(body, [B("L", Id("Nat")),
            B("data", Call("IndexedChain", Id("H"), Id("L"))), .. extra]), true);
    private static Formula ArrayType => Call("G34Array", Id("data"), Id("l"));

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
        "Exact triangle recovery in the prescribed array. All numbered edges, ordered labels and source conditions are retained.",
        H("Exact triangle recovery in the prescribed array"),
        Blocks(
            Item("arrayMiddlePath", "The literal decreasing V diagonal",
                SquareArrayAll(Seq(Call("arrayMiddlePath", Id("g")), Colon, Call("FactorPath", Call("backwardFactors", Call("toChain", Id("data"))), Call("vertex", Call("row", Id("g"), Id("L")), Num(0)), Call("vertex", Call("row", Id("g"), Num(0)), Id("L")))), B("g", Call("G34Array", Id("data"), Id("L")))),
                "Read v_0^(L−1),v_1^(L−2),...,v_(L−1)^0 from this same literal square. Removing its first layer and final column restricts to the same inner triangle; append the original final V_0 edge. The path begins at row(L).vertex(0) and ends at row(0).vertex(L), following backwardFactors(toChain(data)) in decreasing layer order. Every actual V copy and label is retained. At L=0 this is the named nil vertex.", DescribeRole.Definition),
            Item("g34_peelRow", "Forward peeling of the same recurrence row",
                PeelingRowAll(Equal(Call("peelRow", Id("U"), Id("V"), Id("l"), Call("vertex", Id("r"), Num(0)), Call("lastVertex", Id("r")), Call("rowWord", Multiply(Id("U"), Id("V")), Call("successor", Id("l")), Id("r"))),
                    Call("tuple", Call("vertex", Call("next", Id("p")), Num(0)), Call("vertex", Call("next", Id("p")), Id("l")), Call("u", Id("p"), Num(0)), Call("rowWord", Multiply(Id("V"), Id("U")), Id("l"), Call("rowPrefix", Call("next", Id("p")))), Call("v", Id("p"), Id("l"))))),
                "G34FactorStep(U,V,r) means G34Step(UV,VU,U,V,rfl,rfl,r). For a row of length l+1, peelRow returns the tuple (next.vertex(0),next.vertex(l),u(0),rowWord(VU,l,rowPrefix(next)),v(l)). Here rowPrefix deletes the last edge and last vertex, and tuple denotes the nested dependent sigma and product of PeelBoundary. This is the same row’s interior eta word, left U edge and last V edge. The prescribed outer U(l+1) is not used. For l=0 the interior word is nil at next.vertex(0).",
                DescribeRole.Theorem),
            Item("g34_reversePeelRow", "Reverse peeling of the same recurrence row",
                PeelingRowAll(Equal(Call("peelRow", Id("V"), Id("U"), Id("l"), Call("vertex", Call("next", Id("p")), Num(0)), Call("lastVertex", Call("next", Id("p"))), Call("rowWord", Multiply(Id("V"), Id("U")), Call("successor", Id("l")), Call("next", Id("p")))),
                    Call("tuple", Call("vertex", Id("r"), Num(1)), Call("lastVertex", Id("r")), Call("v", Id("p"), Num(0)), Call("rowWord", Multiply(Id("U"), Id("V")), Id("l"), Call("rowTail", Id("r"))), Call("u", Id("p"), Call("successor", Id("l")))))),
                "For the same U,V,r and G34FactorStep p, reverse peeling of next returns (r.vertex(1),r.vertex(l+1),v(0),rowWord(UV,l,rowTail(r)),u(l+1)). The operation rowTail deletes the first edge and first vertex. Tuple has the dependent PeelBoundary type, retaining actual endpoints, labels and independent copy numbers. Thus the saved last U is the originally prescribed right edge of this same legal row, and the inner word is the exact source suffix. At l=0 that suffix is the named nil at r.vertex(1).",
                DescribeRole.Theorem),
            Item("rowFirst_eq_phiRPower", "Both complete evaluations on every actual input",
                OrderedChainAll(Equal(Call("rowFirst", Id("c"), Id("l"), Id("i"), Id("j"), Id("p")),
                    Call("phiRPower", Id("c"), Id("l"), Id("i"), Id("j"), Id("p"))),
                    B("l", Id("Nat")), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("m"))),
                    B("p", Call("WordAndRightBoundary", Id("A"), Id("l"), Call("forwardFactors", Id("c")), Id("i"), Id("j")))),
                "WordAndRightBoundary denotes the sigma over x:Fin n of Word(A,l,i,x) times FactorPath(forwardFactors(c),x,j). For every actual chain c, every finite word length l, every pair of endpoints and every such input p, the complete row-first evaluation equals the right-to-left column-first phiRPower evaluation, including the full output path, word, all endpoint vertices, ordered labels and numbered parallel edges. The proof uses induction on the actual chain to establish the word-successor equation, then induction on word length. It assumes no commuting adjacent functions and no long compatibility law.",
                DescribeRole.Theorem),
            Item("wordToRow", "Read the complete original word as a numbered row",
                RowAll(Seq(Call("wordToRow", Id("A"), Id("l"), Id("i"), Id("j"), Id("w")), Colon, Call("RowWithWord", Id("A"), Id("l"), Id("i"), Id("j"), Id("w"))), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("n"))), B("w", Call("Word", Id("A"), Id("l"), Id("i"), Id("j")))),
                "RowWithWord is the subtype of r:NumberedRow(A,l) with r.vertex(0)=i, r.vertex(l)=j and HEq(rowWord(A,l,r),w). Recursion reads every actual numbered edge of w and keeps its ordered label and intermediate vertex. The zero-word case keeps the original named vertex; it introduces no arbitrary enumeration.", DescribeRole.Definition),
            Item("RightBoundary", "The exact prescribed right-side factor data",
                BoundaryAll(Seq(Call("RightBoundary", Id("data"), Id("i"), Id("j")), Colon, Id("Type")), B("i", Call("Fin", Call("dimension", Id("data"), Num(0)))), B("j", Call("Fin", Call("dimension", Id("data"), Id("L"))))),
                "A RightBoundary(data,i,j) retains vertex(k):Fin(d_k) for every k from 0 through L and edge(k):At(U_k,vertex(k),vertex(k+1)) for every k<L. Its first vertex equals i and its last equals j. Thus every original U factor edge, label and copy is prescribed.", DescribeRole.Definition),
            Item("pathToRightBoundary", "Unpack the entire original R factor path",
                BoundaryAll(Seq(Call("pathToRightBoundary", Id("data"), Id("i"), Id("j"), Id("p")), Colon, Call("RightBoundary", Id("data"), Id("i"), Id("j"))), B("i", Call("Fin", Call("dimension", Id("data"), Num(0)))), B("j", Call("Fin", Call("dimension", Id("data"), Id("L")))), B("p", Call("FactorPath", Call("forwardFactors", Call("toChain", Id("data"))), Id("i"), Id("j")))),
                "Structural recursion on the original indexed chain reads each whole factor-path coordinate. The named nil vertex supplies both boundary endpoints at L=0. A successor retains its actual first U edge and recursively retains the same suffix.", DescribeRole.Definition),
            Item("wordFactorArray", "Generate G34 from the actual word and whole factor path",
                ArrayAll(Seq(Call("wordFactorArray", Id("data"), Id("l"), Id("i"), Id("j"), Id("p")), Colon, ArrayType), B("i", Call("Fin", Call("dimension", Id("data"), Num(0)))), B("j", Call("Fin", Call("dimension", Id("data"), Id("L")))), B("p", Call("OriginalWordAndRightFactorPath", Id("data"), Id("l"), Id("i"), Id("j")))),
                "The input is the sigma over x:Fin(d_0) of Word(A_0,l,i,x) times FactorPath(forwardFactors(toChain(data)),x,j). wordToRow reads its actual top word and pathToRightBoundary reads its full prescribed right U path. Their endpoint proofs provide the required seam, and generateG34 fills the same original indexed recurrence.", DescribeRole.Definition),
            Item("arrayRightPath", "The entire original right U column",
                ArrayAll(Seq(Call("arrayRightPath", Id("g")), Colon, Call("RightColumnFactorPath", Id("data"), Id("l"), Id("g"))), B("g", ArrayType)),
                "RightColumnFactorPath has factors forwardFactors(toChain(data)), source row(0).vertex(l) and target row(L).vertex(l). It reads u_l^0,...,u_l^(L-1), transported only by each nextRow equality; the zero-length column is the named nil vertex.", DescribeRole.Definition),
            Item("g34_rowFirst", "All rows evaluate this same full array",
                ArrayAll(Equal(Call("rowFirst", Call("toChain", Id("data")), Id("l"), Call("topSource", Id("g")), Call("bottomTarget", Id("g")), Call("arrayInput", Id("g"))), Call("arrayOutput", Id("g"))), B("g", ArrayType)),
                "For every original IndexedChain data, every finite width l and every legal G34Array g, arrayInput is (row(0).vertex(l),rowWord(A_0,l,row(0)),arrayRightPath(g)). Its endpoints are topSource=row(0).vertex(0) and bottomTarget=row(L).vertex(l). The complete rowFirst algorithm returns exactly arrayOutput(g), the left U column and the same full bottom word. Induction passes through each actual varying-dimension layer using its supplied factor equalities.", DescribeRole.Theorem),
            Item("g34_phiRPower", "All columns evaluate that very same full array",
                ArrayAll(Equal(Call("phiRPower", Call("toChain", Id("data")), Id("l"), Call("topSource", Id("g")), Call("bottomTarget", Id("g")), Call("arrayInput", Id("g"))), Call("arrayOutput", Id("g"))), B("g", ArrayType)),
                "For the identical data,g and complete prescribed input just defined, the actual right-to-left column-first phiRPower evaluation returns that same arrayOutput. The equality includes all factor edges, bottom-row edges, group labels and copy numbers. It uses the proved complete row/column equality, with no assumed long law or commutation principle.", DescribeRole.Theorem),
            Item("wordFactorArray_top", "The actual input word is the generated top word",
                ArrayAll(Call("HEq", Call("rowWord", Call("A", Id("data"), Num(0)), Id("l"), Call("row", Call("wordFactorArray", Id("data"), Id("l"), Id("i"), Id("j"), Id("p")), Num(0))), Call("inputWord", Id("p"))), B("i", Call("Fin", Call("dimension", Id("data"), Num(0)))), B("j", Call("Fin", Call("dimension", Id("data"), Id("L")))), B("p", Call("OriginalWordAndRightFactorPath", Id("data"), Id("l"), Id("i"), Id("j")))),
                "For every actual typed input p, the top row of wordFactorArray reads back its full original word p.second.first. HEq accounts for the reconstructed endpoint proofs and preserves every actual numbered edge. The proof consumes both the exact generated top-row identity and the wordToRow reconstruction law.", DescribeRole.Theorem),
            Item("g34_psi0", "The literal top triangle recovers R and S",
                SquareArrayAll(Equal(Call("inverseTopTriangle", Id("data"), Id("g")),
                    Call("tuple", Call("vertex", Call("row", Id("g"), Id("L")), Num(0)), Call("arrayLeftPath", Id("g")), Call("arrayMiddlePath", Id("g")))), B("g", Call("G34Array", Id("data"), Id("L")))),
                "For every source square g, inverseTopTriangle means psi0(toChain(data),row(0).vertex(0),row(0).vertex(L)) inverse applied to rowWord(A_0,L,row(0)). Its result is exactly (row(L).vertex(0),R_out,S_mid), where R_out=arrayLeftPath(g) reads u_0^0 through u_0^(L−1) and S_mid=arrayMiddlePath(g) reads v_0^(L−1),v_1^(L−2),...,v_(L−1)^0. The entire sigma equality includes every endpoint, ordered label and copy. At L=0 it recovers the named nil vertex.", DescribeRole.Theorem),
            Item("g34_psiL", "The literal bottom triangle recovers S and the prescribed R",
                SquareArrayAll(Equal(Call("inverseBottomTriangle", Id("data"), Id("g")),
                    Call("tuple", Call("vertex", Call("row", Id("g"), Num(0)), Id("L")), Call("arrayMiddlePath", Id("g")), Call("arrayRightPath", Id("g")))), B("g", Call("G34Array", Id("data"), Id("L")))),
                "InverseBottomTriangle is psiL(toChain(data),row(L).vertex(0),row(L).vertex(L)) inverse applied to the complete bottom Word(A_L,L,row(L)). It yields exactly (row(0).vertex(L),S_mid,R_in), with the identical diagonal S_mid and the original prescribed right path u_L^0,...,u_L^(L−1). Induction removes the last actual source layer and first column, uses reverse peeling of that same row, prepends its literal left V and appends its original right U. The path identities agree with the existing decreasing V and increasing U paths. No supplied bottom-boundary identity is used.", DescribeRole.Theorem),
            Item("g34_longR", "Both triangles and the sweep on the same square",
                SquareArrayAll(Equal(Call("sweepOfTopTriangleAndRight", Id("data"), Id("g")),
                    Call("leftAndBottomTriangle", Id("data"), Id("g"))), B("g", Call("G34Array", Id("data"), Id("L")))),
                "Let i=row(0).vertex(0),x=row(0).vertex(L),y=row(L).vertex(0),j=row(L).vertex(L). Write R=R_out,S=S_mid,Rprime=R_in. Then phiRPower(c,L,i,j)(x,psi0(c,i,x)(y,R,S),Rprime)=(y,R,psiL(c,y,j)(x,S,Rprime)), with c=toChain(data). This is the literal whole-square equation on its actual three boundary paths. It follows from the two inverse triangle identities and the complete column evaluation.", DescribeRole.Theorem),
            Item("reverseChain_snoc", "Reverse an appended original step",
                SnocAll(Equal(Call("reverseChain", Snoc), Call("ChainCons", Id("V"), Id("U"), Id("hC"), Id("hB"), Call("reverseChain", Id("c"))))),
                "Reversing the appended U,V step places the actual exchanged V,U step first, with hC,hB in that order, followed by the same reversed original chain.", DescribeRole.Theorem))));
}
