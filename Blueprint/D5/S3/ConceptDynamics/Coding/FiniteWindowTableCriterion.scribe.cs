using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FiniteWindowTableCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Instances(Formula body, params Formula[] instances)
    {
        var items = new List<Formula>();
        foreach (var instance in instances)
            items.AddRange([OpenBracket, instance, CloseBracket, Comma, Sp]);
        items.Add(body);
        return Seq([.. items]);
    }
    private static Formula.BoundVariable[] Carriers => [
        B("V", F.Id("Type")), B("E", F.Id("Type")),
        B("W", F.Id("Type")), B("D", F.Id("Type"))];
    private static Formula[] FiniteGraphs => [
        Call("Fintype", F.Id("V")), Call("Fintype", F.Id("E")),
        Call("DecidableEq", F.Id("V")), Call("Fintype", F.Id("W")),
        Call("Fintype", F.Id("D")), Call("DecidableEq", F.Id("W"))];
    private static Formula[] DiscreteEdges => [
        Call("TopologicalSpace", F.Id("E")), Call("DiscreteTopology", F.Id("E")),
        Call("TopologicalSpace", F.Id("D")), Call("DiscreteTopology", F.Id("D")),
        Call("Nonempty", F.Id("V")), Call("Nonempty", F.Id("W"))];
    private static Formula.BoundVariable[] Graphs => [
        B("G", Call("DirectedMultigraph", F.Id("V"), F.Id("E"))),
        B("F", Call("DirectedMultigraph", F.Id("W"), F.Id("D")))];
    private static Formula.BoundVariable[] RadiiAndPair => [
        B("p", F.Id("Nat")), B("q", F.Id("Nat")), B("r", F.Id("Nat")), B("s", F.Id("Nat")),
        B("pair", Call("TablePair", F.Id("G"), F.Id("F"),
            F.Id("p"), F.Id("q"), F.Id("r"), F.Id("s")))];
    private static Formula EssentialGraphs => And(Call("Essential", F.Id("G")),
        Call("Essential", F.Id("F")));
    private static Formula Parameters(Formula body) => All(Instances(
        All(Imp(EssentialGraphs, body), [.. Graphs, .. RadiiAndPair]),
        [.. FiniteGraphs, .. DiscreteEdges]), Carriers);
    private static Formula EquivariantParameters(Formula body) => All(Instances(
        All(Imp(EssentialGraphs, body), [.. Graphs,
            B("AG", Call("GraphAction", F.Id("Gamma"), F.Id("G"))),
            B("AF", Call("GraphAction", F.Id("Gamma"), F.Id("F"))), .. RadiiAndPair]),
        [.. FiniteGraphs, .. DiscreteEdges, Call("Group", F.Id("Gamma")),
            Call("MulAction", F.Id("Gamma"), F.Id("V")),
            Call("MulAction", F.Id("Gamma"), F.Id("E")),
            Call("MulAction", F.Id("Gamma"), F.Id("W")),
            Call("MulAction", F.Id("Gamma"), F.Id("D"))]),
        [.. Carriers, B("Gamma", F.Id("Type"))]);
    private static Formula FailureParameters(Formula body)
    {
        Formula complete = And(
            All(new Formula.Relation(F.Id("e"), FormulaRelationOperator.MemberOf, F.Id("edgesG")),
                B("e", F.Id("E"))),
            All(new Formula.Relation(F.Id("d"), FormulaRelationOperator.MemberOf, F.Id("edgesF")),
                B("d", F.Id("D"))));
        return All(Instances(All(Imp(And(complete, EssentialGraphs), body),
            [.. Graphs, .. RadiiAndPair,
                B("edgesG", Call("List", F.Id("E"))), B("edgesF", Call("List", F.Id("D")))]),
            [.. FiniteGraphs, Call("DecidableEq", F.Id("E")), Call("DecidableEq", F.Id("D"))]),
            Carriers);
    }
    private static Formula Pair => F.Id("pair");
    private static Formula Local => Call("LocalCriterion", Pair);
    private static Formula Conjugacy => Call("SameTableConjugacy", Pair);


    private static Formula SquareParameters(Formula body) => All(Instances(All(body,
        B("n", F.Id("Nat")), B("A", Call("GroupMat", F.Id("H"), F.Id("n"), F.Id("n")))),
        Call("Group", F.Id("H"))), B("H", F.Id("Type")));
    private static Formula OrderedSquareParameters(Formula body) => All(Instances(All(body,
        B("n", F.Id("Nat")), B("A", Call("GroupMat", F.Id("H"), F.Id("n"), F.Id("n")))),
        Call("Group", F.Id("H")), Call("Fintype", F.Id("H")), Call("LinearOrder", F.Id("H"))),
        B("H", F.Id("Type")));
    private static Formula OrderedParameters(Formula body) => All(Instances(All(body,
        B("n", F.Id("Nat")), B("m", F.Id("Nat")),
        B("U", Call("GroupMat", F.Id("H"), F.Id("n"), F.Id("m"))),
        B("V", Call("GroupMat", F.Id("H"), F.Id("m"), F.Id("n")))),
        Call("Group", F.Id("H")), Call("Fintype", F.Id("H")), Call("LinearOrder", F.Id("H"))),
        B("H", F.Id("Type")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four concrete word tests characterize the same arbitrary pair of finite-window tables as mutually inverse continuous maps commuting with the original unit shift.",
        H("Complete arbitrary-table criterion"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-window-iff"), DeclarationHandle.Create(Prefix + "original23_1"),
                H("Exactly the supplied tables on all histories"),
                StatementSource.FromAuthor(Disp(Parameters(Iff(Local, Call("Nonempty", Conjugacy))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The independent natural radii p,q,r,s may all be zero. Write m=p+q+1, n=r+s+1 and N=p+q+r+s+1. TablePair contains arbitrary f:LegalWord(G,m) to D and g:LegalWord(F,n) to E; it imposes no encoding hypothesis. SeamG checks every m+1 edge word and equates target(f(slice(word,0,m))) with source(f(slice(word,1,m))). SeamF is the corresponding n+1 edge equation for g.")),
                    Paragraph(Text("For every G word of length N, mapBlock applies f to the n windows starting at j=0 through n minus 1. Its legality is proved from seamG before g is applied. The equation then says g(mapBlock(f,word))=word[p+r]. The F test applies g to the m windows starting at j=0 through m minus 1, proves legality from seamF, and says f(mapBlock(g,word))=word[p+r]. Both input intervals are exactly [-p-r,q+s]. Proof irrelevance makes the equations independent of the seam-proof choice.")),
                    Paragraph(Text("SameTableConjugacy carries two legal-history maps with pointwise bindings Phi(x)[i]=f(historyWindow(G,x,i-p,m)) and Psi(y)[i]=g(historyWindow(F,y,i-r,n)). It also carries both inverse equations, continuity in the product subspace topology of discrete actual edges, and both commutation laws with the shift x[i] to x[i+1]. Necessity extends each prescribed word by its incoming and outgoing tails. Its actual occurrences force both seam equations and both center recoveries. The same f and g occur in all these statements."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-group-iff"), DeclarationHandle.Create(Prefix + "original23_1_equivariant"),
                H("Local and global equivariance for the same maps"),
                StatementSource.FromAuthor(Disp(EquivariantParameters(Iff(
                    And(Local, And(Call("LocalEquivariant", F.Id("AG"), Call("f", Pair)),
                        Call("LocalEquivariant", F.Id("AF"), Call("g", Pair)))),
                    Exists("c", Conjugacy, And(
                        Call("GlobalEquivariant", F.Id("AG"), F.Id("AF"), Call("forward", F.Id("c"))),
                        Call("GlobalEquivariant", F.Id("AF"), F.Id("AG"), Call("backward", F.Id("c"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("GraphAction states source and target preservation for the supplied vertex and edge actions. Word and history actions act on each actual edge. LocalEquivariant quantifies every group element and every window, with f(a acting on word)=a acting on f(word), and likewise for g. GlobalEquivariant states the same equality for the same history maps. Necessity realizes each word; the chosen tails need not themselves be equivariant. The equivalence holds for any group, and the finite algorithm uses a finite group."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-certified-inspection"), DeclarationHandle.Create(Prefix + "rejected_candidate_has_finite_witness"),
                H("Terminating finite checks with actual failure facts"),
                StatementSource.FromAuthor(Disp(FailureParameters(
                    Iff(new Formula.Not(Local), Exists("bad", Call("FailureWitness", Pair),
                        Call("FailureExposure", F.Id("bad"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("With decidable vertex and edge equality, legalWordFintype enumerates exactly the subtype of finite edge tuples satisfying adjacency, and tablePairFintype enumerates every pair of actual functions. The seam tests run before the dependent roundtrip tests. finiteTableExists decides existence at fixed radii by finite quantification over these table pairs. originalExistenceDecidable transports that executable decision to existence of a SameTableConjugacy; the analogous finite-group functions include all group/window equations.")),
                    Paragraph(Text("For certificate extraction the caller supplies complete finite edge lists and a complete group list. tupleWords recursively enumerates tuples; enumerateWords keeps exactly legal words, with a proved completeness theorem. List.choose scans these explicit lists for a failing fact. Every FailureWitness contains a word and the actual failed seam or recovery equality, including the seam proofs needed to type a recovery. EquivariantFailure adds the actual group element, window and failed action equality. The inspector returns either all test proofs or the failed finite test. The rejection theorem equates rejection with existence of such a concrete failure exposed in an actual history; the corresponding finite-group theorem includes group/window failures and their history occurrences. No arbitrary classical Decidable, sampling criterion or graph-only uniform bound on radii is asserted.")),
                    Paragraph(Text("Loops, parallel edges, disconnected essential components and asymmetric windows are allowed. Every tested word has positive length; a vertex-free empty edge tuple does not specify a zero-edge path."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-counted-expansion"), DeclarationHandle.Create(Prefix + "countedExpansion"),
                H("Actual free expansion"), StatementSource.FromAuthor(Disp(SquareParameters(Call("DirectedMultigraph",Call("Prod",Call("Fin",F.Id("n")),F.Id("H")),Call("Prod",Call("Edge",F.Id("A")),F.Id("H")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For any square natural group-ring matrix A, the vertex of an expanded edge (e,h) is (source(e),h), and its target is (target(e),h times label(e)). This definition is definitionally equal to the existing FixedBlockRigidity.expandedGraph; it imposes no commutativity and forgets no numbered edge."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orderedforward"), DeclarationHandle.Create(Prefix + "orderedForward"),
                H("orderedForward"), StatementSource.FromAuthor(Disp(OrderedParameters(new Formula.TypeArrow(Call("LegalWord",Call("countedExpansion",Call("product",F.Id("U"),F.Id("V"))),Num(2)),Call("Prod",Call("Edge",Call("product",F.Id("V"),F.Id("U"))),F.Id("H")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For the legal two-edge word ((a0,h0),(a1,h1)), split both edges in the prescribed UV order as (u0,v0),(u1,v1). Return (joinVU(v0,u1),h0 times label(u0)). Adjacency supplies the actual shared vertex for joining. This crosses the first actual U half-edge."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orderedbackward"), DeclarationHandle.Create(Prefix + "orderedBackward"),
                H("orderedBackward"), StatementSource.FromAuthor(Disp(OrderedParameters(new Formula.TypeArrow(Call("LegalWord",Call("countedExpansion",Call("product",F.Id("V"),F.Id("U"))),Num(2)),Call("Prod",Call("Edge",Call("product",F.Id("U"),F.Id("V"))),F.Id("H")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The two input edges are preceding and central output. Split them in VU order as (vMinus,u0),(v0,u1). Return (joinUV(u0,v0),k0 times label(u0) inverse), where k0 is the coordinate of the SECOND input edge. The shared U half-edge is constructed by splitting the preceding output, not assumed as an inverse map."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orderedoverlapinput"), DeclarationHandle.Create(Prefix + "orderedOverlapInput"),
                H("orderedOverlapInput"), StatementSource.FromAuthor(Disp(OrderedParameters(Call("TablePair",Call("countedExpansion",Call("product",F.Id("U"),F.Id("V"))),Call("countedExpansion",Call("product",F.Id("V"),F.Id("U"))),Num(0),Num(1),Num(1),Num(0))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This TablePair uses orderedForward and orderedBackward on the actual free expansions of UV and VU, at forward radii (0,1) and inverse radii (1,0). The associated recovery words have three edges and center index one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("d8rank"), DeclarationHandle.Create(Prefix + "d8Rank"),
                H("d8Rank"), StatementSource.FromAuthor(Disp(new Formula.TypeArrow(Call("DihedralGroup",Num(4)),F.Id("Nat")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("d8Rank(r i)=i.val and d8Rank(sr i)=4+(-i).val. Since sr i denotes s times r to i, this is exactly e,r,r squared,r cubed,s,rs,r squared s,r cubed s. This rank is injective, so d8Order lifts the natural order through it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("d8order"), DeclarationHandle.Create(Prefix + "d8Order"),
                H("d8Order"), StatementSource.FromAuthor(Disp(Call("LinearOrder",Call("DihedralGroup",Num(4))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The total order is lifted through the injective d8Rank. It is a finite group order for labels and does not claim a multiplication-compatible group order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("d8p"), DeclarationHandle.Create(Prefix + "d8P"),
                H("d8P"), StatementSource.FromAuthor(Disp(Call("GroupMat",Call("DihedralGroup",Num(4)),Num(1),Num(1)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("In the source order the scalar factor P has coefficients [1,2,1,1,1,1,1,0]. Each nonzero coefficient is a literal MonoidAlgebra.single summand; the r cubed s coefficient is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("d8q"), DeclarationHandle.Create(Prefix + "d8Q"),
                H("d8Q"), StatementSource.FromAuthor(Disp(Call("GroupMat",Call("DihedralGroup",Num(4)),Num(1),Num(1)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The scalar factor Q is the sum of the literal unit-labelled and s-labelled singleton coefficients, each one. Its vector is [1,0,0,0,1,0,0,0]."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orderedd8input"), DeclarationHandle.Create(Prefix + "orderedD8Input"),
                H("orderedD8Input"), StatementSource.FromAuthor(Disp(Call("TablePair",Call("countedExpansion",Call("product",F.Id("d8P"),F.Id("d8Q"))),Call("countedExpansion",Call("product",F.Id("d8Q"),F.Id("d8P"))),Num(0),Num(1),Num(1),Num(0)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The tables use these literal factors, their actual products and prescribed split ranks. They have forward radii (0,1) and inverse radii (1,0), as in orderedOverlapInput."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("d8groups"), DeclarationHandle.Create(Prefix + "d8Groups"),
                H("d8Groups"), StatementSource.FromAuthor(Disp(Call("List",Call("DihedralGroup",Num(4))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The complete dictionary is [r0,r1,r2,r3,sr0,sr3,sr2,sr1], exactly the prescribed order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orderededges"), DeclarationHandle.Create(Prefix + "orderedEdges"),
                H("orderedEdges"), StatementSource.FromAuthor(Disp(OrderedSquareParameters(Call("List",Call("Prod",Call("Edge",F.Id("A")),F.Id("H")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a square matrix A, enumerate group coordinate h, source i, target j, label g in their supplied finite orders, then every c in Fin(coeff(A[i,j],g)). The list contains every actual expanded numbered edge, including every nonzero fiber and no element of an empty fiber. The complete list supplies the edge alphabets for finite inspection."))), DescribeRole.Definition))));
}
