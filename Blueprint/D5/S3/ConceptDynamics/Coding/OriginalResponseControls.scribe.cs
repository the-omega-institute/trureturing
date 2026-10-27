using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class OriginalResponseControlsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original balanced maps control quotient essentiality, node orders and the same first diamond factors.",
        H("Quantitative response controls"),
        Blocks(
            Paragraph(Text("All dimensions n, k and the lag m range over natural numbers. A and B are square natural count matrices of orders n and k; R has shape n by k and S has shape k by n. Essential means that every row and every column has a nonzero entry. The original input consists of essential A and B, positive lag m, and four numbered equivalence families: phiR(i,z): EdgePair(A,R,i,z) \u2243 EdgePair(R,B,i,z); phiS(t,w): EdgePair(B,S,t,w) \u2243 EdgePair(S,A,t,w); psiA(i,j): EdgePair(R,S,i,j) \u2243 FinitePath(A,m,i,j); psiB(t,z): EdgePair(S,R,t,z) \u2243 FinitePath(B,m,t,z). Both original BalancedA(phiR,phiS,psiA) and BalancedB(phiR,phiS,psiB) identities are required. NumberedEdgePairEquiv and NumberedPathEquiv in the displays abbreviate precisely these indexed families. No quotient control, factor bound or resulting trace is supplied as an input.")),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.balanced_sweep"),
                H("The balanced sweep identity"), StatementSource.FromAuthor(FormulaDsl.Disp(Original(All(Equal(Call("sweep",Id("phiR"),Id("alpha"),Id("r")),Call("balancedBoundary",Id("psiA"),Id("psiB"),Id("alpha"),Id("r"))),B("i",Fin(N)),B("j",Fin(N)),B("z",Fin(K)),B("alpha",Call("FinitePath",A,M,Id("i"),Id("j"))),B("r",Fin(Call("entry",R,Id("j"),Id("z")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For alpha from i to j and a numbered R edge r from j to z, write psiA(i,j)\u207b\u00b9(alpha)=(u,r\u2080,s\u2080). The balancedBoundary expression is the dependent triple (u,r\u2080,psiB(u,z)(j,s\u2080,r)). The sweep along phiR equals this triple. Row essentiality and the path equivalences supply the auxiliary numbered edges, and the two balance identities identify the boundary and tail. This reconstructs the compatibility field used below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.NodeControl"),
                H("Controls on an actual node"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Equal(Call("NodeControl",Id("X"),Id("q"),Id("bound")),Conjoin(Le(Id("r"),Id("q")),Call("Essential",Id("X")),All(Le(Call("entry",Id("X"),Id("i"),Id("j")),Id("bound")),B("i",Fin(Id("r"))),B("j",Fin(Id("r")))))),B("r",Nat),B("X",Mat(Id("r"),Id("r"))),B("q",Nat),B("bound",Nat)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("NodeControl(X,q,bound) consists of order(X) \u2264 q, a nonzero entry in every row, a nonzero entry in every column, and X(i,j) \u2264 bound for every entry. The two essentiality clauses are separate obligations. When the order is zero their universal clauses are vacuous; no inhabitant is chosen."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.ResponseControl"),
                H("Controls at every response depth"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Equal(Call("ResponseControl",Id("L"),Id("q"),Id("bound")),And(Call("AllNumberedResponseNodesControlled",Id("L"),Id("q"),Id("bound")),Call("AllNumberedResponseFactorsControlled",Id("L"),Call("max",Num(1),Id("bound"))))),B("p",Nat),B("A",Mat(Id("p"),Id("p"))),B("Q",Id("Type")),B("L",Call("IncomingLift",A,Id("Q"))),B("q",Nat),B("bound",Nat)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural depth d, every natural r, and every equivalence e: Quotient(L.response d) \u2243 Fin r, the reindexed incomingResponseMatrix has NodeControl(q,bound). For every additional numbering f at d+1, set U=reindex(e,f,incomingResponseU L d) and V=reindex(f,e,incomingResponseV L d). The two numbered matrices equal U V and V U respectively, and each entry of both U and V is at most max(1,bound). These are the actual fiber-count and membership matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_response_controls"),
                H("Essential and bounded response quotients"), StatementSource.FromAuthor(FormulaDsl.Disp(Compatible(Conjoin(Call("ResponseControl",Call("squareIncomingLift",C),Q,Bound),Call("ResponseControl",Call("squareOutgoingLift",C),Q,Bound),Call("AllTransposedOutgoingNodesControlled",C,Q,Bound))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any compatible certificate c, the incoming and outgoing square lifts satisfy ResponseControl with q=card(Edge R) and bound=max(card(Edge A),card(Edge B)). Every numbered outgoing quotient, after transpose, has the same NodeControl. To prove essentiality at arbitrary depth, an outgoing lifted edge from a representative supplies an inhabited incoming response fiber; fiber-cardinality transport moves the witness to the chosen quotient representative. For a prescribed target class, an incoming base edge supplies a fiber member. The actual square graph supplies these lift witnesses. Cardinal surjection and subtype bounds then give the order and entry bounds."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-5"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_order_identity"),
                H("The square graph order"), StatementSource.FromAuthor(FormulaDsl.Disp(Compatible(And(Equal(Q,Call("sumEntries",R)),Le(Call("max",N,K),Q))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Numbered R edges correspond bijectively to the dependent sum over i,j of Fin(R(i,j)), so q is the sum of all R entries. Surjectivity of the original source and target projections gives n \u2264 q and k \u2264 q. These cardinal identities retain both projections."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-6"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.powerMaximum"),
                H("The maximum power entry"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Equal(Call("powerMaximum",A,M),Call("finiteSupPowerEntries",A,M)),B("n",Nat),B("A",Mat(N,N)),B("m",Nat)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("powerMaximum(A,m) is Finset.univ.sup of (A^m)(i,j) over Fin n \u00d7 Fin n. Its value is zero for n=0. For positive order it is the ordinary maximum of the entries of A^m."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-pathcount"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.numbered_path_count"),
                H("Counting numbered paths"), StatementSource.FromAuthor(FormulaDsl.Disp(All(And(Call("Finite",Call("FinitePath",A,Id("d"),Id("i"),Id("j"))),Equal(Call("NatCard",Call("FinitePath",A,Id("d"),Id("i"),Id("j"))),Call("entry",Call("power",A,Id("d")),Id("i"),Id("j")))),B("n",Nat),B("A",Mat(N,N)),B("d",Nat),B("i",Fin(N)),B("j",Fin(N))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite numbered length-d paths from i to j have cardinality (A^d)(i,j), also for d=0 and empty dimensions. At zero length the fiber is a singleton exactly when the endpoints agree. At a successor length, split off the first numbered edge and count the dependent sum over its target. This is the existing counting argument used by the square-order bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-factorbound"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.factor_entry_upper"),
                H("The individual factor bound"), StatementSource.FromAuthor(FormulaDsl.Disp(Raw(Imp(Conjoin(Call("RowEssential",BB),Call("HasNumberedPathEquiv",R,S,A,M),Call("HasNumberedPathEquiv",S,R,BB,M)),All(Le(Call("entry",R,Id("i"),Id("j")),Call("powerMaximum",A,M)),B("i",Fin(N)),B("j",Fin(K))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("RowEssential(B) means a nonzero entry in every row of B. For arbitrary R and S with the two displayed numbered path equivalences, each entry R(i,j) is bounded by powerMaximum(A,m). Recover an S edge from the inverse B-path bijection and inject the R fiber into the corresponding A-path fiber. Counting paths and taking the maximum proves the inequality. This factors the existing square_order_upper argument so that the same bound also supplies the unrestricted finite search."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-7"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_order_upper"),
                H("The quantitative square-order bound"), StatementSource.FromAuthor(FormulaDsl.Disp(Compatible(Le(Q,Multiply(Multiply(N,K),Call("powerMaximum",A,M)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a numbered S edge leaving each target vertex. Pairing it with an R edge and applying psiA injects that R fiber into a length-m A-path fiber. The standard path count is (A^m)(i,l), hence each R entry is at most powerMaximum(A,m). Summing over n times k entries gives the displayed bound, including empty dimensions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-8"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_diamond_controls"),
                H("Bounds on the same diamond factors"), StatementSource.FromAuthor(FormulaDsl.Disp(Compatible(Ex(Conjoin(Equal(Call("leftFirstMatrix",C),Multiply(Call("intersection",C),Id("D"))),Equal(Call("rightFirstMatrix",C),Multiply(Id("D"),Call("intersection",C))),Call("EntryBound",Call("intersection",C),Call("max",Q,Bound)),Call("EntryBound",Id("D"),Call("max",Q,Bound))),B("D",Mat(Call("rightFirstOrder",C),Call("leftFirstOrder",C))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let IL and IJ be first-left column membership and first-right row membership, SL and SJ their representative selectors, and P=IL IJ. The leftFirstMatrix is IL C SL and rightFirstMatrix is SJ C IJ for C=c.squareMatrix. FirstResponseDiamond supplies one D satisfying IL C SL=P D and SJ C IJ=D P. Every P entry is at most q. For a column h of P, choose u=firstRightRep(h) and g=firstLeftClass(u). The u summand gives P(g,h)\u22651, so D(h,f)\u2264P(g,h)D(h,f)\u2264(P D)(g,f)\u2264bound\u2264max(q,bound). The conclusion bounds this same D with both factor equations. It does not assert a representative-entry formula for D."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalresponsecontrols-9"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalResponseControls.originalBalancedResponseControls"),
                H("Controls from the original four maps"), StatementSource.FromAuthor(FormulaDsl.Disp(Original(And(Quantities(),Call("BothResponseLegControls",Call("balancedCertificate",A,BB,R,S,M,Id("phiR"),Id("phiS"),Id("psiA"),Id("psiB")),Q,Bound))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Construct c internally with the original matrices, positive lag, essentiality and numbered maps; balanced_sweep provides its compatibility equation. The result gives q=sumEntries(R), max(n,k)\u2264q\u2264n k powerMaximum(A,m), both ResponseControl clauses, and all transposed outgoing NodeControls. BothResponseLegControls abbreviates exactly these three response conclusions. The certificate and these conclusions are derived from the original telescope."))), DescribeRole.Theorem),
            Paragraph(Text("The quotient-fiber argument and the same-D inequality use the original numbered square construction. Path counting, cardinal transport, the square graph projections and the unbounded first diamond are supplied by the imported results and mathlib. The statement concerns fixed positive lag; independent least forgetting depths and a literal representative formula for D are separate questions.")))));

    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula body, params Formula.BoundVariable[] vars) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] vars) => new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Conjoin(params Formula[] terms) { var v = terms[^1]; for (var i = terms.Length - 2; i >= 0; --i) v = And(terms[i], v); return v; }
    private static Formula N => Id("n"); private static Formula K => Id("k"); private static Formula M => Id("m");
    private static Formula A => Id("A"); private static Formula BB => Id("B"); private static Formula R => Id("R"); private static Formula S => Id("S");
    private static Formula Nat => Id("Nat"); private static Formula Fin(Formula x) => Call("Fin", x);
    private static Formula Mat(Formula a, Formula b) => Call("CountMat", a, b);
    private static Formula C => Id("c"); private static Formula Q => Call("cardEdge", R);
    private static Formula Bound => Call("max", Call("cardEdge", A), Call("cardEdge", BB));
    private static Formula Raw(Formula body) => All(body, B("n", Nat), B("k", Nat), B("m", Nat), B("A", Mat(N,N)), B("B", Mat(K,K)), B("R", Mat(N,K)), B("S", Mat(K,N)));
    private static Formula Compatible(Formula body) => Raw(All(body, B("c", Call("CompatibleCertificate", A, BB, R, S, M))));
    private static Formula Original(Formula body) => Raw(All(Imp(Conjoin(Call("Essential", A), Call("Essential", BB), Le(Num(1),M), Call("BalancedA",Id("phiR"),Id("phiS"),Id("psiA")), Call("BalancedB",Id("phiR"),Id("phiS"),Id("psiB"))), body),
        B("phiR",Call("NumberedEdgePairEquiv",A,R,R,BB)), B("phiS",Call("NumberedEdgePairEquiv",BB,S,S,A)),
        B("psiA",Call("NumberedPathEquiv",R,S,A,M)), B("psiB",Call("NumberedPathEquiv",S,R,BB,M))));
    private static Formula Quantities() => Conjoin(Equal(Q,Call("sumEntries",R)),Le(Call("max",N,K),Q),Le(Q,Multiply(Multiply(N,K),Call("powerMaximum",A,M))));

}
