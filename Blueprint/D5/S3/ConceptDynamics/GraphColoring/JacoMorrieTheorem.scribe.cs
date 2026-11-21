using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoMorrieTheoremDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Morrie's theorem on the finite Jaco graphs holds once n = R_k is added to its indegree conditions.",
        H("Morrie's theorem with the endpoint condition"),
        Blocks(
            Node("jaco-morrie-indeg", "The indegree d^-(v_i)", "indeg",
                Disp(Equal(Call("indeg", F.Id("i")), Subtract(F.Id("i"), Call("b", F.Id("i"))))),
                "indeg i is the indegree a_i=i-b_i of v_i in the infinite Jaco graph, where b_i=beattyOut i=floor((i+1)/phi) is its outdegree.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-morrie-result", "Corrected Morrie's theorem", "result", ResultFormula(),
                "Write J_n for the complete set of maximum-degree labels of the finite linear Jaco graph J_n(1), R_k=jacoRight k=k+b_k, and P(n,k) for the hypothesis that n is at least 2 and k is the least element of J_n, the prime Jaconian vertex. Under P(n,k), k=Delta_n by JacoMaximumSet.result, and J_n={k} exactly when n=R_k and b_(k+1)=b_k+1, that is, when d^-(v_k)=d^-(v_(k+1)). At a singleton, J_(n+1) is [k,k+1] or [k,k+2], and by the degree formula deg(v_(k+2))=min(k+2,n+1-b_(k+2)) at order n+1=R_k+1 the label k+2 is maximum exactly when b_(k+2)=b_(k+1), that is, when d^-(v_(k+2))=d^-(v_(k+1))+1; otherwise b_(k+2)=b_(k+1)+1 and d^-(v_(k+2))=d^-(v_(k+1)). Hence (a) n=R_k, d^-(v_k)=d^-(v_(k+1)) and d^-(v_(k+2))=d^-(v_(k+1))+1 if and only if J_n={k} and J_(n+1)={k,k+1,k+2}; since the outdegrees never stay constant over two consecutive steps (2/phi>1), d^-(v_(k+2))=d^-(v_(k+1))+1 already forces d^-(v_k)=d^-(v_(k+1)), so n=R_k with d^-(v_(k+2))=d^-(v_(k+1))+1 is equivalent to the same conclusion; and (b) n=R_k and d^-(v_k)=d^-(v_(k+1))=d^-(v_(k+2)) if and only if J_n={k} and J_(n+1)={k,k+1}. Theorem 2.3 (Morrie's Theorem) of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, page 4, states (a) and (b) without the condition n=R_k, and both then fail (JacoMorrieTheoremRefutation); Corollary 4 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, gives the corrected form. The maximum-set description used through JacoMaximumSet is credited there to Patel's solution of MathDB problem 369424, which was not inspected.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var k1 = Add(k, D(1));
        var k2 = Add(k, D(2));
        var endpoint = Equal(n, Call("R", k));
        var flat = Equal(Indeg(k), Indeg(k1));
        var rise = Equal(Indeg(k2), Add(Indeg(k1), D(1)));
        var condB = And(flat, Equal(Indeg(k1), Indeg(k2)));
        var setA = And(Equal(J(n), Set(k)), Equal(J(Add(n, D(1))), Set(Seq(k, Comma, Sp, k1, Comma, Sp, k2))));
        var setB = And(Equal(J(n), Set(k)), Equal(J(Add(n, D(1))), Set(Seq(k, Comma, Sp, k1))));
        var body = And(Iff(And(endpoint, And(flat, rise)), setA), And(Iff(And(endpoint, rise), setA),
            Iff(And(endpoint, condB), setB)));
        return Disp(All("n", Nat(), All("k", Nat(), Imp(Call("P", n, k), body))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Indeg(Formula i) => Call("indeg", i);
    private static Formula J(Formula n) => Call("jaconian", n);
    private static Formula Set(Formula a) => Seq(F.OpenBrace, a, F.CloseBrace);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
