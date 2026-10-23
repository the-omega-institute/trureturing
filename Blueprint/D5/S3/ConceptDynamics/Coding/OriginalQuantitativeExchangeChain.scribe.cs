using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class OriginalQuantitativeExchangeChainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Controlled Type traces retain actual factors, tags and all node controls at exact length 2m minus one.",
        H("Quantitative exchange traces"),
        Blocks(
            Paragraph(Text("All dimensions n, k and the lag m range over natural numbers. A and B are square natural count matrices of orders n and k; R has shape n by k and S has shape k by n. Essential means that every row and every column has a nonzero entry. The original input consists of essential A and B, positive lag m, and four numbered equivalence families: phiR(i,z): EdgePair(A,R,i,z) \u2243 EdgePair(R,B,i,z); phiS(t,w): EdgePair(B,S,t,w) \u2243 EdgePair(S,A,t,w); psiA(i,j): EdgePair(R,S,i,j) \u2243 FinitePath(A,m,i,j); psiB(t,z): EdgePair(S,R,t,z) \u2243 FinitePath(B,m,t,z). Both original BalancedA(phiR,phiS,psiA) and BalancedB(phiR,phiS,psiB) identities are required. NumberedEdgePairEquiv and NumberedPathEquiv in the displays abbreviate precisely these indexed families. No quotient control, factor bound or resulting trace is supplied as an input.")),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.factorBound"),
                H("Ordinary and diamond bounds"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Equal(Call("factorBound",Id("q"),Id("bound"),Id("tag")),Call("ifThenElse",Id("tag"),Call("max",Id("q"),Id("bound")),Call("max",Num(1),Id("bound")))),B("q",Nat),B("bound",Nat),B("tag",Id("Bool"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A true tag marks the diamond step and gives max(q,bound); a false tag marks an ordinary response step and gives max(1,bound)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.ControlledChain"),
                H("A dependent data trace"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Call("TypeTrace",Id("q"),Id("bound"),Id("X"),Id("Y"),Id("length")),B("q",Nat),B("bound",Nat),B("a",Nat),B("b",Nat),B("X",Mat(Id("a"),Id("a"))),B("Y",Mat(Id("b"),Id("b"))),B("length",Nat)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ControlledChain q bound X Y length is an inductive Type. A nil node stores X and its NodeControl, has endpoint X and length zero. A cons stores the actual rectangular U and V, its Boolean tag, both entry bounds, NodeControl(U V), and a tail from V U to the endpoint. The source is U V and the length is tail length plus one. Thus the final node remains controlled even for an empty trace."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.erase"),
                H("Erasing the controls"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Call("ExchangeChain",Id("X"),Id("Y"),Id("length")),B("q",Nat),B("bound",Nat),B("a",Nat),B("b",Nat),B("X",Mat(Id("a"),Id("a"))),B("Y",Mat(Id("b"),Id("b"))),B("length",Nat),B("trace",Call("ControlledChain",Id("q"),Id("bound"),Id("X"),Id("Y"),Id("length")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Erasure recursively uses each stored U and V to construct the ordinary ExchangeChain. It discards the controls and tags while keeping the factor matrices on the same sequence of exchanges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.sourceControl"),
                H("The source node is controlled"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Call("NodeControl",Id("X"),Id("q"),Id("bound")),B("q",Nat),B("bound",Nat),B("a",Nat),B("b",Nat),B("X",Mat(Id("a"),Id("a"))),B("Y",Mat(Id("b"),Id("b"))),B("length",Nat),B("trace",Call("ControlledChain",Id("q"),Id("bound"),Id("X"),Id("Y"),Id("length")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Case analysis reads the control stored by nil or cons. Reversal uses the tail source control when adjoining the reversed last exchange."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-5"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.trans"),
                H("Concatenating actual traces"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Call("ControlledChain",Id("q"),Id("bound"),Id("X"),Id("Z"),Add(Id("l1"),Id("l2"))),B("q",Nat),B("bound",Nat),B("a",Nat),B("b",Nat),B("c",Nat),B("X",Mat(Id("a"),Id("a"))),B("Y",Mat(Id("b"),Id("b"))),B("Z",Mat(Id("c"),Id("c"))),B("l1",Nat),B("l2",Nat),B("left",Call("ControlledChain",Id("q"),Id("bound"),Id("X"),Id("Y"),Id("l1"))),B("right",Call("ControlledChain",Id("q"),Id("bound"),Id("Y"),Id("Z"),Id("l2")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The structurally recursive local function traverses the left trace, retaining each factor pair, tag and control, and replaces its nil tail by the right trace. Length transport uses addition identities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-6"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.reverse"),
                H("Reversing actual traces"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Call("ControlledChain",Id("q"),Id("bound"),Id("Y"),Id("X"),Id("length")),B("q",Nat),B("bound",Nat),B("a",Nat),B("b",Nat),B("X",Mat(Id("a"),Id("a"))),B("Y",Mat(Id("b"),Id("b"))),B("length",Nat),B("trace",Call("ControlledChain",Id("q"),Id("bound"),Id("X"),Id("Y"),Id("length")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reversal recursively reverses the tail and appends the exchanged pair (V,U) with its original tag and swapped bounds. This reverses tag order, preserves length and gives the original source as the final controlled node."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-7"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.transpose"),
                H("Transposing actual traces"), StatementSource.FromAuthor(FormulaDsl.Disp(All(Call("ControlledChain",Id("q"),Id("bound"),Call("transpose",Id("X")),Call("transpose",Id("Y")),Id("length")),B("q",Nat),B("bound",Nat),B("a",Nat),B("b",Nat),B("X",Mat(Id("a"),Id("a"))),B("Y",Mat(Id("b"),Id("b"))),B("length",Nat),B("trace",Call("ControlledChain",Id("q"),Id("bound"),Id("X"),Id("Y"),Id("length")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transpose recursively sends (U,V) to (V transpose,U transpose) and keeps tag order. It exchanges the row and column essentiality clauses of each node control. Concatenation, reversal and transpose recurse on the uncast tail through local indexed functions; their definitions use structural recursion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-8"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.compatibleControlledChain"),
                H("The controlled fixed-lag chain"), StatementSource.FromAuthor(FormulaDsl.Disp(Compatible(Call("Nonempty",Call("ControlledChain",Q,Bound,A,BB,Subtract(Multiply(Num(2),M),Num(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m\u22652, compose the reversed left response leg, the one-step diamond and the transposed right leg. The diamond uses exactly the D and both product equations supplied by square_diamond_controls; its bound supplies the actual middle V bound. For m=1, simultaneously renumber the two endpoints of that same diamond. The lengths total 2m\u22121. No positive dimension is added."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalquantitativeexchangechain-9"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.originalBalancedQuantitativeExchangeChain"),
                H("Quantitative traces from the original maps"), StatementSource.FromAuthor(FormulaDsl.Disp(Original(And(Quantities(),Ex(Call("Nonempty",Call("ErasureFiber",Id("trace"))),B("trace",Call("ControlledChain",Q,Bound,A,BB,Subtract(Multiply(Num(2),M),Num(1))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original four maps and both balance identities construct the compatible certificate internally. One obtains q=sumEntries(R), max(n,k)\u2264q\u2264n k powerMaximum(A,m), and an actual trace in ControlledChain(q,bound,A,B,2m\u22121). ErasureFiber(trace) is the subtype of ordinary ExchangeChain values equal to trace.erase; it is inhabited by trace.erase itself. Thus the ordinary chain and the controlled trace use the same factor data."))), DescribeRole.Theorem),
            Paragraph(Text("The single and single_reindex constructors build the one actual diamond step, using both endpoint controls and both factor equations. controlled_response_chain_to recursively uses the original incomingResponseU and incomingResponseV at every response depth and allows the prescribed final numbering. These constructions preserve empty dimensions and the nil terminal control. They do not supply an executable finite-table exporter, independent forgetting depths, a minimum-lag characterization or further original sections beyond this fixed-lag result.")))));

    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula body, params Formula.BoundVariable[] vars) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] vars) => new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Conjoin(params Formula[] terms) { var v = terms[^1]; for (var i = terms.Length - 2; i >= 0; --i) v = And(terms[i], v); return v; }
    private static Formula N => Id("n"); private static Formula K => Id("k"); private static Formula M => Id("m");
    private static Formula A => Id("A"); private static Formula BB => Id("B"); private static Formula R => Id("R"); private static Formula S => Id("S");
    private static Formula Nat => Id("Nat");
    private static Formula Mat(Formula a, Formula b) => Call("CountMat", a, b);
    private static Formula Q => Call("cardEdge", R);
    private static Formula Bound => Call("max", Call("cardEdge", A), Call("cardEdge", BB));
    private static Formula Raw(Formula body) => All(body, B("n", Nat), B("k", Nat), B("m", Nat), B("A", Mat(N,N)), B("B", Mat(K,K)), B("R", Mat(N,K)), B("S", Mat(K,N)));
    private static Formula Compatible(Formula body) => Raw(All(body, B("c", Call("CompatibleCertificate", A, BB, R, S, M))));
    private static Formula Original(Formula body) => Raw(All(Imp(Conjoin(Call("Essential", A), Call("Essential", BB), Le(Num(1),M), Call("BalancedA",Id("phiR"),Id("phiS"),Id("psiA")), Call("BalancedB",Id("phiR"),Id("phiS"),Id("psiB"))), body),
        B("phiR",Call("NumberedEdgePairEquiv",A,R,R,BB)), B("phiS",Call("NumberedEdgePairEquiv",BB,S,S,A)),
        B("psiA",Call("NumberedPathEquiv",R,S,A,M)), B("psiB",Call("NumberedPathEquiv",S,R,BB,M))));
    private static Formula Quantities() => Conjoin(Equal(Q,Call("sumEntries",R)),Le(Call("max",N,K),Q),Le(Q,Multiply(Multiply(N,K),Call("powerMaximum",A,M))));

}
