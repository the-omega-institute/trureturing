using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FixedBlockRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FixedBlockRigidity.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Id(string s) => F.Id(s);
    private static Formula Graph(string s) => Id(s);
    private static Formula History(Formula g) => Call("History", g);
    private static Formula Word(Formula g) => Call("LegalWord", g, Id("k"));
    private static Formula Equiv(Formula a, Formula b) => Call("Equiv", a, b);
    private static Formula EdgeAt(Formula x, Formula i) => Call("historyEdge", x, i);
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula ConstructedMap => Call("blockHomeomorph", Id("hk"), Id("f"), Id("endpoints"));
    private static Formula StepLaw(Formula g, Formula f) => All(
        Equal(Apply(ConstructedMap, Call("shift", g, Id("x"))),
            Call("shift", f, Apply(ConstructedMap, Id("x")))), B("x", History(g)));
    private static Formula.BoundVariable[] BlockData(Formula g, Formula f) => [
        B("k", Id("Nat")), B("hk", Call("NatPositive", Id("k"))),
        B("f", Equiv(Word(g), Word(f))),
        B("endpoints", Call("PreservesBlockEndpoints", Id("hk"), Id("f"))),
        B("hstep", StepLaw(g, f))];
    private static Formula General => All(
        Exists("gamma", Equiv(Id("E"), Id("D")), And(
            All(Equal(EdgeAt(Apply(ConstructedMap, Id("x")), Id("i")),
                Apply(Id("gamma"), EdgeAt(Id("x"), Id("i")))),
                B("x", History(Graph("G"))), B("i", Id("Int"))),
            All(And(Equal(Call("source", Graph("F"), Apply(Id("gamma"), Id("e"))),
                    Call("source", Graph("G"), Id("e"))),
                Equal(Call("target", Graph("F"), Apply(Id("gamma"), Id("e"))),
                    Call("target", Graph("G"), Id("e")))), B("e", Id("E"))))),
        [B("V", Id("Type")), B("E", Id("Type")), B("D", Id("Type")),
         B("G", Call("DirectedMultigraph", Id("V"), Id("E"))),
         B("F", Call("DirectedMultigraph", Id("V"), Id("D"))),
         B("finiteV", Call("Fintype", Id("V"))), B("finiteE", Call("Fintype", Id("E"))),
         B("finiteD", Call("Fintype", Id("D"))), B("equalityV", Call("DecidableEq", Id("V"))),
         B("topologyE", Call("TopologicalSpace", Id("E"))), B("discreteE", Call("DiscreteTopology", Id("E"))),
         B("topologyD", Call("TopologicalSpace", Id("D"))), B("discreteD", Call("DiscreteTopology", Id("D"))),
         B("hG", Call("Essential", Graph("G"))), B("hF", Call("Essential", Graph("F"))),
         .. BlockData(Graph("G"), Graph("F"))]);
    private static Formula GroupClause => All(Equal(Id("A"), Id("B")),
        [B("H", Id("Type")), B("group", Call("Group", Id("H"))),
         B("finiteH", Call("Fintype", Id("H"))), B("n", Id("Nat")),
         B("topologyH", Call("TopologicalSpace", Id("H"))), B("discreteH", Call("DiscreteTopology", Id("H"))),
         B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
         B("B", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
         B("hA", Call("Essential", Call("baseGraph", Id("A")))),
         B("hB", Call("Essential", Call("baseGraph", Id("B")))),
         .. BlockData(Call("expandedGraph", Id("A")), Call("expandedGraph", Id("B")))]);

    private static Formula EqualPowerMap => Call("equalPowerHomeomorph", Id("A"), Id("B"), Id("hk"), Id("hpower"));
    private static Formula EqualPowerCounts => Call("equalPowerFiberCounts", Id("A"), Id("B"), Id("hk"), Id("hpower"));
    private static Formula AttachmentClause => All(And(
        All(Equal(Call("original181History", Id("A"), Id("B"), Id("hk"), EqualPowerCounts, Id("x")),
            Apply(EqualPowerMap, Id("x"))), B("x", History(Call("expandedGraph", Id("A"))))),
        And(All(Equal(Apply(EqualPowerMap, Call("groupHistory", Id("A"), Id("a"), Id("x"))),
            Call("groupHistory", Id("B"), Id("a"), Apply(EqualPowerMap, Id("x")))),
            B("a", Id("H")), B("x", History(Call("expandedGraph", Id("A"))))),
        And(All(Equal(Apply(EqualPowerMap, Call("iterate", Call("shift", Call("expandedGraph", Id("A"))), Id("k"), Id("x"))),
            Call("iterate", Call("shift", Call("expandedGraph", Id("B"))), Id("k"), Apply(EqualPowerMap, Id("x")))),
            B("x", History(Call("expandedGraph", Id("A"))))),
        new Formula.Logic(All(Equal(Apply(EqualPowerMap, Call("shift", Call("expandedGraph", Id("A")), Id("x"))),
            Call("shift", Call("expandedGraph", Id("B")), Apply(EqualPowerMap, Id("x")))),
            B("x", History(Call("expandedGraph", Id("A"))))), FormulaLogicOperator.Implies, Equal(Id("A"), Id("B")))))),
        B("H", Id("Type")), B("group", Call("Group", Id("H"))), B("finiteH", Call("Fintype", Id("H"))),
        B("n", Id("Nat")), B("topologyH", Call("TopologicalSpace", Id("H"))), B("discreteH", Call("DiscreteTopology", Id("H"))),
        B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))), B("B", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
        B("hA", Call("Essential", Call("baseGraph", Id("A")))), B("hB", Call("Essential", Call("baseGraph", Id("B")))),
        B("k", Id("Nat")), B("hk", Call("NatPositive", Id("k"))),
        B("hpower", Equal(Call("matrixPower", Id("A"), Id("k")), Call("matrixPower", Id("B"), Id("k")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed disjoint block substitution that also respects unit time is induced by an actual-edge bijection at every position.",
        H("Original18.3: fixed block rigidity"),
        Blocks(
            Describe.Lean(DescribeId.Create("original18-3-edge-rigidity"),
                DeclarationHandle.Create(Prefix + "original18_3"), H("The same code is one-block"),
                StatementSource.FromAuthor(Disp(General)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("G and F are finite essential directed multigraphs on the same vertex type V. Parallel edges remain distinct. NatPositive(k) means 0<k. For positive k, f is the actual bijection of legal k-edge words. PreservesBlockEndpoints states equality of source at index 0 and target at index k minus 1 for every word. FixedBlockLaw quantifies every input history x and integer block index j and identifies the output window starting at jk with f of the input window starting at jk. It therefore binds the exact fixed alignment [jk,(j+1)k-1], the exact f and the exact h.")),
                    Paragraph(Text("Only the original one-step shift equation is assumed. Integer translations are derived. Two histories sharing their edge at zero can be spliced using one past and the other future. The forward window identifies the output with one history; the shifted last-coordinate window identifies it with the other. Thus the output at zero depends only on the actual input edge. Essentiality realizes every edge, and the inverse block bijection yields the inverse edge map. Boundary-source preservation and adjacency then give both endpoint equations.")),
                    Paragraph(Text("The map h is blockHomeomorph(hk,f,endpoints), constructed using integer quotient and remainder at every positive and negative position. Legality is proved inside blocks and at their actual endpoint seams. The inverse uses f inverse on the same aligned blocks, and both maps are continuous because each coordinate reads one finite word. The only dynamical premise is unit-shift commutation of this exact constructed map; no separately assumed history equivalence, continuity or inverse-locality premise is added. No strong connectivity, unique edge between vertices, symmetric window, positive mixing or pre-assumed one-block inverse is required. The k=1 case is included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original18-3-free-expansion"),
                DeclarationHandle.Create(Prefix + "original18_3_freeExpansion"), H("Literal equality of group-ring matrices"),
                StatementSource.FromAuthor(Disp(GroupClause)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("GroupMat has natural group-ring coefficients. An expanded actual edge is (e,a), where e retains source, target, label and parallel-edge number; its endpoints are (e.source,a) and (e.target,a*e.label). Essentiality of the base graph constructs incoming and outgoing actual edges at every expanded vertex. Vertices retain the same base index and the same group coordinate on both sides.")),
                    Paragraph(Text("For each i,j and g, the actual edges from (i,1) to (j,g) are in explicit bijection with Fin(coeff(A[i,j],g)). Restricting the edge bijection from original18_3 to these exact endpoint fibers equates every coefficient with B. Hence A=B as natural group-ring matrices, rather than merely equality of augmentation, spectrum, high powers or unlabeled edge counts. The equal-power attachment constructs the word bijection and ordered-coordinate lift from the explicit premise A^k=B^k, identifies its operational output with blockHomeomorph, and establishes H-equivariance and the k-step law. For finite H and essential base graphs, InertGroupBlockConjugacy.original18_1 derives equal powers from inertness of the actual stationary dimension-group actions of A and B and equal augmentation matrices. Its tau is the least positive uniformizing exponent. For every rational decomposition W and positive n, it proves max(tau(A),tau(B)) <= n*bH(W). For a nontrivial finite group and positive n, it supplies an actual augmentation-first rational decomposition with the original nontrivial matrix orders. Every k at or above the tau threshold has the rational expression and this same equal-power attachment; the trivial-group and zero-size boundaries remain separate. Equivariance is not an additional premise of the endpoint-count theorem.")),
                    Paragraph(Text("This excludes the specified fixed nonoverlapping block scheme when A differs from B. It does not exclude overlapping windows, another state presentation or another original-time conjugacy."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equal-power-ordered-block-attachment"),
                DeclarationHandle.Create(Prefix + "equalPower_attachment"), H("The actual equal-power construction"),
                StatementSource.FromAuthor(Disp(AttachmentClause)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("matrixPower is natural matrix exponentiation, iterate is Function.iterate, and equalPowerFiberCounts denotes the proved fiber_counts_of_equal_power proof at A,B,k. For each positive k with the explicit natural matrix equality A^k=B^k, the actual ordered-label word fibers have equal cardinality. Separate finite choices construct the base word map, and the initial group coordinate uniquely determines its ordered lift. The direct quotient-and-remainder output equals equalPowerHomeomorph at every integer coordinate. Left group action and k-step time commute with this same map, and one-step commutation of this map implies A=B. The premise A^k=B^k remains explicit in equalPower_attachment. Under its essentiality, inertness and equal-augmentation hypotheses, InertGroupBlockConjugacy.original18_1 proves the bridge from the actual dimension-group action through the least positive tau to the rational n*bH(W) cutoff and supplies this premise at every admissible exponent. Its attachment uses the exact equalPowerHomeomorph at that exponent; one-step commutation of a different map does not imply the rigidity conclusion."))), DescribeRole.Theorem))));
}
