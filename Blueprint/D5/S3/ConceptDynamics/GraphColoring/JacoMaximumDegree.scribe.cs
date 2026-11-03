using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoMaximumDegreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2025jaco");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary maximum degree of every positive-order recursive linear Jaco graph is its same-index literal Zeckendorf deletion.",
        H("Maximum degree and literal Fibonacci digit deletion"),
        Blocks(
            Node("degree", "degree_formula", "Count both kinds of neighbors",
                "For every natural n and every vertex v with label i from 1 through n, the ordinary undirected degree is min(i,n-b(i)), where b(i) is floor((i+1)/phi). The incoming labels are the interval from b(i) through i-1. The outgoing labels are i+1 through min(n,i+b(i)). These disjoint intervals count the actual neighbor set of the existing recursive graph.",
                Disp(Bound("n", Naturals(), Bound("v", Call("Vertex", N),
                    Equal(Call("degree", Call("jaco", N), F.Id("v")),
                        Call("min", Call("val", F.Id("v")), Subtract(N,
                            Call("beattyOut", Call("val", F.Id("v")))))))))),
            Node("family", "max_degree_eq_deletion", "Every positive graph order",
                "For n at least two, let k be the deletion value. The substitution block inequalities, together with the proved endpoint law, give R_k at most n and R_(k+1) greater than n. Vertex k has degree k. Smaller labels have degree at most their labels; larger labels have degree at most n-b(k+1), which is at most k. At order one, the graph is a singleton and deleting its word 1 gives zero. This retains the actual sequence index n and introduces no graph at order zero.",
                Disp(Family())),
            Node("complete", "result", "Both clauses of Conjecture 2.2",
                "Kok's Conjecture 2.2 asserts the displayed floor formula for every order n at least two, identifies the same-index A319433 term, and retains every positive order in its p-graphical family. The sequence operation is independently defined on canonical Zeckendorf digits; it is not defined by the floor expression. Thus the fixed family J_1,J_2,... realizes every positive-index term, and restricting this identity realizes every positive finite prefix. The offset-zero sequence entry stays outside the printed graph family. The graph proof uses recursive interval counting; Bettina's prose theorem is not a formal premise.",
                Disp(And(Bound("n", Naturals(), Implies(LessEqual(D(2), N),
                    And(Equal(DeltaN(), FloorN()), Equal(DeltaN(), DeleteN())))), Family())),
                claim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kok-linear-jaco-maximum-degree"),
                    ResolutionKind.Proved)))));

    private static Formula N => F.Id("n");
    private static Formula DeltaN() => Call("maxDegree", Call("jaco", N));
    private static Formula DeleteN() => Call("deleteLeast", N);
    private static Formula FloorN() => Subtract(Call("natFloor", Divide(Multiply(D(2), Add(N, D(2))),
        Add(D(1), Call("sqrt", D(5))))), D(1));
    private static Formula Family() => Bound("n", Naturals(), Implies(LessEqual(D(1), N),
        Equal(DeltaN(), DeleteN())));
    private static Formula Divide(Formula a, Formula b) => Seq(Par(a), Slash, Par(b));
    private static DocumentBlock Node(string id, string declaration, string title, string prose, Formula formula,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("jaco-maximum-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, claim);

    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Bound(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula LessEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
}
