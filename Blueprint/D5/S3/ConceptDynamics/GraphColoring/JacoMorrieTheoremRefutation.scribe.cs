using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoMorrieTheoremRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each part of Morrie's theorem on the finite Jaco graphs fails as stated: part (a) at order 6 and part (b) at order 4.",
        H("Morrie's theorem as stated is false"),
        Blocks(
            Node("jaco-morrie-claim", "Morrie's theorem as stated, part (a) or part (b)", "claim", ClaimFormula(),
                "Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 4, Theorem 2.3 (Morrie's Theorem): if J_n(1), n at least 2, has prime Jaconian vertex v_k (Definition 1.4: the least Jaconian vertex) then (a) d^-(v_k)=d^-(v_(k+1)) and d^-(v_(k+2))=d^-(v_(k+1))+1 if and only if J(J_n)={v_k} and J(J_(n+1)(1))={v_k,v_(k+1),v_(k+2)}, and (b) d^-(v_k)=d^-(v_(k+1))=d^-(v_(k+2)) if and only if J(J_n)={v_k} and J(J_(n+1)(1))={v_k,v_(k+1)}. Here d^-(v_i)=indeg i=i-b_i is the indegree in the infinite Jaco graph and P(n,k) says that n is at least 2 and k is the least element of J_n. The claim is the disjunction of the two parts, so refuting it refutes each part separately.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaco-morrie-refuted", "Refutation of both parts", "result", Disp(new Formula.Not(F.Id("claim"))),
                "With 0.618<1/phi<0.619, b_2=1, b_3=2, b_4=3 and b_5=3, and JacoAdditionLaw.delta_eq_floor gives Delta_4=2 and Delta_6=3, which are the least maximum-degree labels by JacoMaximumSet.result. At n=6, k=3 the indegrees d^-(v_3)=d^-(v_4)=1 and d^-(v_5)=2 satisfy the left side of (a), but J_6 is not {3} because the singleton criterion of JacoMaximumSet.result requires 6=R_3=3+b_3=5. At n=4, k=2 the indegrees d^-(v_2)=d^-(v_3)=d^-(v_4)=1 satisfy the left side of (b), but J_4 is not {2} because R_2=3. Corollary 4 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, records both counterexamples; the corrected theorem is JacoMorrieTheorem.result.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var k1 = Add(k, D(1));
        var k2 = Add(k, D(2));
        var condA = And(Equal(Indeg(k), Indeg(k1)), Equal(Indeg(k2), Add(Indeg(k1), D(1))));
        var condB = And(Equal(Indeg(k), Indeg(k1)), Equal(Indeg(k1), Indeg(k2)));
        var setA = And(Equal(J(n), Set(k)), Equal(J(Add(n, D(1))), Set(Seq(k, Comma, Sp, k1, Comma, Sp, k2))));
        var setB = And(Equal(J(n), Set(k)), Equal(J(Add(n, D(1))), Set(Seq(k, Comma, Sp, k1))));
        var partA = All("n", Nat(), All("k", Nat(), Imp(Call("P", n, k), Iff(condA, setA))));
        var partB = All("n", Nat(), All("k", Nat(), Imp(Call("P", n, k), Iff(condB, setB))));
        return Disp(Equal(F.Id("claim"), new Formula.Logic(Par(partA), FormulaLogicOperator.Or, Par(partB))));
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
