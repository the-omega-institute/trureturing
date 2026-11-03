using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoAdditionLawRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct orders three and eleven refute the complete original two-branch Jaco addition assertion.",
        H("The original Jaco addition law is false"),
        Blocks(
            Node("jaco-addition-unique", "A unique Jaconian vertex", "UniqueJaconian", UniqueFormula(),
                "UniqueJaconian n means exactly one vertex of jaco n attains its ordinary maximum degree. The carrier consists precisely of positive labels 1 through n. This is uniqueness of a vertex within one graph, not uniqueness of a numerical degree across graph orders. The graph is the existing finite truncation of the recursive rule i<j<=2i-d^-(v_i), with orientation forgotten; every edge has exactly one forward arc, so simple degree counts incoming and retained outgoing arcs together.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaco-addition-claim", "The whole original Theorem 2.10", "claim", ClaimFormula(),
                "Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 7, Theorem 2.10 (Conjectured), assert both displayed branches for every ordered pair of distinct natural orders n,m at least three. The first branch uses inclusive OR: either graph having a unique Jaconian vertex suffices. Otherwise means neither has a unique Jaconian vertex. No cutoff or additional graph hypothesis is imposed. The explicit open-problem list on printed page 11 asks to prove this theorem.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaco-addition-refuted", "Refutation of the complete addition assertion", "result", Disp(new Formula.Not(F.Id("claim"))),
                "Use the original graph and the existing JacoMaximumDegree.degree_formula and JacoMaximumDegree.result. Put phi=(1+sqrt(5))/2. Exact rational bounds 8/5<phi<13/8 give the needed floors. The three degrees of J_3 are 1,2,1, so its unique maximizing vertex is v_2 and its maximum is 2. The same maximum-degree formula gives maximum 7 for J_11 and maximum 8 for J_14. At the admissible pair (3,11), the first branch therefore requires 8=2+7, a contradiction. A failure at this pair negates the whole universal two-branch claim; it asserts neither failure at every pair nor a counterexample to the otherwise branch. These numerical values also occur in Kok's prior published arXiv:2507.16500v1 Table 1; they are not new numerical data. Bounded source searches leave literature gaps and establish no worldwide priority.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("kok-jaco-addition-law-refutation"), ResolutionKind.Refuted)))));

    private static Formula UniqueFormula()
    {
        var n = F.Id("n");
        var v = F.Id("v");
        var w = F.Id("w");
        var vertex = Call("Vertex", n);
        var unique = Ex("v", vertex, And(Equal(Degree(n, v), Delta(n)),
            All("w", vertex, Imp(Equal(Degree(n, w), Delta(n)), Equal(w, v)))));
        return Disp(All("n", Nat(), Iff(U(n), unique)));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var first = Imp(Or(U(n), U(m)), Equal(Delta(Add(n, m)), Add(Delta(n), Delta(m))));
        var second = Imp(And(new Formula.Not(U(n)), new Formula.Not(U(m))),
            Equal(Delta(Add(n, m)), Add(Add(Delta(n), Delta(m)), D(1))));
        return Disp(Iff(F.Id("claim"), All("n", Nat(), All("m", Nat(),
            Imp(Le(D(3), n), Imp(Le(D(3), m), Imp(NotEqual(n, m), And(first, second))))))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula U(Formula n) => Call("UniqueJaconian", n);
    private static Formula Delta(Formula n) => Call("maxDegree", Call("jaco", n));
    private static Formula Degree(Formula n, Formula v) => Call("degree", Call("jaco", n), v);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Ex(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
}
