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
    private static Formula Parameters(Formula body) => All(body,
        B("V", F.Id("Type")), B("E", F.Id("Type")), B("W", F.Id("Type")), B("D", F.Id("Type")),
        B("finiteV", Call("Fintype", F.Id("V"))), B("nonemptyV", Call("Nonempty", F.Id("V"))),
        B("finiteE", Call("Fintype", F.Id("E"))), B("equalityV", Call("DecidableEq", F.Id("V"))),
        B("finiteW", Call("Fintype", F.Id("W"))), B("nonemptyW", Call("Nonempty", F.Id("W"))),
        B("finiteD", Call("Fintype", F.Id("D"))), B("equalityW", Call("DecidableEq", F.Id("W"))),
        B("topologyE", Call("TopologicalSpace", F.Id("E"))),
        B("discreteE", Call("DiscreteTopology", F.Id("E"))),
        B("topologyD", Call("TopologicalSpace", F.Id("D"))),
        B("discreteD", Call("DiscreteTopology", F.Id("D"))),
        B("G", Call("DirectedMultigraph", F.Id("V"), F.Id("E"))),
        B("F", Call("DirectedMultigraph", F.Id("W"), F.Id("D"))),
        B("essentialG", Call("Essential", F.Id("G"))), B("essentialF", Call("Essential", F.Id("F"))),
        B("p", F.Id("Nat")), B("q", F.Id("Nat")), B("r", F.Id("Nat")), B("s", F.Id("Nat")),
        B("pair", Call("TablePair", F.Id("G"), F.Id("F"), F.Id("p"), F.Id("q"), F.Id("r"), F.Id("s"))));
    private static Formula FailureParameters(Formula body) => All(body,
        B("V", F.Id("Type")), B("E", F.Id("Type")), B("W", F.Id("Type")), B("D", F.Id("Type")),
        B("finiteV", Call("Fintype", F.Id("V"))), B("finiteE", Call("Fintype", F.Id("E"))),
        B("finiteW", Call("Fintype", F.Id("W"))), B("finiteD", Call("Fintype", F.Id("D"))),
        B("equalityV", Call("DecidableEq", F.Id("V"))), B("equalityW", Call("DecidableEq", F.Id("W"))),
        B("equalityE", Call("DecidableEq", F.Id("E"))), B("equalityD", Call("DecidableEq", F.Id("D"))),
        B("G", Call("DirectedMultigraph", F.Id("V"), F.Id("E"))),
        B("F", Call("DirectedMultigraph", F.Id("W"), F.Id("D"))),
        B("essentialG", Call("Essential", F.Id("G"))), B("essentialF", Call("Essential", F.Id("F"))),
        B("p", F.Id("Nat")), B("q", F.Id("Nat")), B("r", F.Id("Nat")), B("s", F.Id("Nat")),
        B("pair", Call("TablePair", F.Id("G"), F.Id("F"), F.Id("p"), F.Id("q"), F.Id("r"), F.Id("s"))),
        B("edgesG", Call("List", F.Id("E"))), B("edgesF", Call("List", F.Id("D"))),
        B("completeG", All(new Formula.Relation(F.Id("e"), FormulaRelationOperator.MemberOf,
            F.Id("edgesG")), B("e", F.Id("E")))),
        B("completeF", All(new Formula.Relation(F.Id("d"), FormulaRelationOperator.MemberOf,
            F.Id("edgesF")), B("d", F.Id("D")))));
    private static Formula Pair => F.Id("pair");
    private static Formula Local => Call("LocalCriterion", Pair);
    private static Formula Conjugacy => Call("SameTableConjugacy", Pair);

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
                    Paragraph(Text("SameTableConjugacy carries two legal-history maps with pointwise bindings Phi(x)[i]=f(historyWindow(G,x,i-p,m)) and Psi(y)[i]=g(historyWindow(F,y,i-r,n)). It also carries both inverse equations, continuity in the product subspace topology of discrete actual edges, and both commutation laws with the shift x[i] to x[i+1]. Necessity uses the retained two-tail realizer on each prescribed word. Its actual occurrences force both seam equations and both center recoveries. The same f and g occur in all these statements."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-group-iff"), DeclarationHandle.Create(Prefix + "original23_1_equivariant"),
                H("Local and global equivariance for the same maps"),
                StatementSource.FromAuthor(Disp(Parameters(All(Iff(
                    And(Local, And(Call("LocalEquivariant", F.Id("AG"), Call("f", Pair)),
                        Call("LocalEquivariant", F.Id("AF"), Call("g", Pair)))),
                    Exists("c", Conjugacy, And(
                        Call("GlobalEquivariant", F.Id("AG"), F.Id("AF"), Call("forward", F.Id("c"))),
                        Call("GlobalEquivariant", F.Id("AF"), F.Id("AG"), Call("backward", F.Id("c")))))),
                    B("Gamma", F.Id("Type")), B("group", Call("Group", F.Id("Gamma"))),
                    B("actionV", Call("MulAction", F.Id("Gamma"), F.Id("V"))),
                    B("actionE", Call("MulAction", F.Id("Gamma"), F.Id("E"))),
                    B("actionW", Call("MulAction", F.Id("Gamma"), F.Id("W"))),
                    B("actionD", Call("MulAction", F.Id("Gamma"), F.Id("D"))),
                    B("AG", Call("GraphAction", F.Id("Gamma"), F.Id("G"))),
                    B("AF", Call("GraphAction", F.Id("Gamma"), F.Id("F"))))))),
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
                    Paragraph(Text("Loops, parallel edges, disconnected essential components and asymmetric windows stay in scope. All checked word lengths are positive; no statement identifies a zero-edge path with a vertex-free empty edge tuple. The parameter specialization 23.2 introduces no retained wrapper. The unsupported 21.3 claim and the existing matrix-chain construction are outside this module. Authored formulas summarize the exact declarations using the defined record names; SDK admission, script execution and rendering alone do not establish semantic equivalence or canonical admission."))), DescribeRole.Theorem))));
}
