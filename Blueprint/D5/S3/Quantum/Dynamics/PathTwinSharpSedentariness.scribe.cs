using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PathTwinSharpSedentarinessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/monterde2023sedentariness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In the graph P'_9, the path on vertices 1 to 9 with an extra vertex 10 joined to vertex 2, the return amplitude of the quantum walk U(t) = exp(itA) at vertex 1 satisfies |U(t)_(1,1)| >= 5/18 for every real t. So vertex 1 is not sharply 1/9-sedentary, which refutes the conjecture of H. Monterde (arXiv:2401.00362) that vertex 1 of P'_n is sharply 1/n-sedentary for every odd n >= 5.",
        H("The twin end vertex of P'_9 is not sharply 1/9-sedentary"),
        Blocks(
            Node("path-twin", "The graph P'_n", PathTwinFormula(),
                "The adjacency matrix of P'_n on the vertices 1, ..., n + 1: the entry is 1 on the edges and 0 elsewhere, where the edges are those of the path 1, 2, ..., n and the edge between vertex 2 and vertex n + 1, so that vertices 1 and n + 1 are non-adjacent twins. In the formal statement vertex j is the index j - 1 of Fin (n + 1).",
                "pathTwin", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sharp", "Sharp sedentariness", SharpFormula(),
                "For the quantum walk U(t) = exp(itA), a vertex u is sharply C-sedentary when 0 < C <= 1 and the infimum over t > 0 of |U(t)_(u,u)| equals C. The formal statement writes exp(itA) as the propagator exp(-isA) at s = -t.",
                "SharplySedentary", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "The conjecture of the paper: for every odd n >= 5, vertex 1 of P'_n is sharply 1/n-sedentary.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture fails at n = 9", Disp(new Formula.Not(F.Id("claim"))),
                "Let A be the adjacency matrix of P'_9 and put theta_k = (2k + 1) pi/18 for k = 0, ..., 8. For each k the vector with entries 1/2, cos(theta_k), cos(2 theta_k), ..., cos(8 theta_k), 1/2 is an eigenvector of A for the eigenvalue 2 cos(theta_k); the last row uses cos(9 theta_k) = 0. The vector e_1 - e_10 lies in the kernel of A. The closed form sin(a/2) times the sum of cos(ak + b) over k < 9 equals sin(9a/2) cos(4a + b), with a = m pi/9 and b = m pi/18, gives sin(m pi/2) cos(m pi/2) = sin(m pi)/2 = 0, so the sum of cos(m theta_k) over k vanishes for m = 1, ..., 8, and so e_1 = (e_1 - e_10)/2 plus one ninth of the sum of the nine eigenvectors. The matrix exponential acts on each eigenvector by the scalar exponential, which gives U(t)_(1,1) = 1/2 + (1/18) times the sum of exp(2it cos(theta_k)). Pairing theta_k with pi - theta_k, this equals 5/9 + (1/9)(cos(alpha t) + cos(sqrt(3) t) + cos(beta t) + cos(gamma t)) with alpha = 2 cos(pi/18), beta = 2 cos(5 pi/18) and gamma = 2 cos(7 pi/18). Because cos(pi/3) = 1/2, alpha = beta + gamma. For real a and b, cos a + cos b + cos(a + b) >= -3/2, since (1 + cos a + cos b)^2 + (sin a - sin b)^2 = 3 + 2(cos a + cos b + cos(a + b)). Hence U(t)_(1,1) >= 5/9 - (1/9)(3/2 + 1) = 5/18 for every real t, and the infimum over t > 0 is at least 5/18, which is larger than 1/9.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("monterde-2023-path-twin-sharp-sedentariness"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("sedentary-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula AllOf(Formula variables, Formula body) =>
        Seq(Forall, Sp, variables, Comma, Sp, body);
    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        new Formula.Apply(matrix, [row, column]);
    private static Formula Plus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula PathTwinFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        Formula entry = Entry(Call(F.Id("pathTwin"), n), i, j);
        Formula pathEdge = And(Equal(Plus(i, D(1)), j), Rel(j, FormulaRelationOperator.LessThan, n));
        Formula pathEdgeBack = And(Equal(Plus(j, D(1)), i), Rel(i, FormulaRelationOperator.LessThan, n));
        Formula twinEdge = And(Equal(i, D(1)), Equal(j, n));
        Formula twinEdgeBack = And(Equal(i, n), Equal(j, D(1)));
        Formula edge = Or(Or(pathEdge, pathEdgeBack), Or(twinEdge, twinEdgeBack));
        Formula ones = Implies(edge, Equal(entry, D(1)));
        Formula zeros = Implies(new Formula.Not(Parenthesized(edge)), Equal(entry, D(0)));
        return Disp(And(ones, zeros));
    }

    private static Formula SharpFormula()
    {
        Formula a = F.Id("A"), u = F.Id("u"), c = F.Id("C"), t = F.Id("t");
        Formula amplitude = new Formula.Norm(
            Call(F.Id("hamiltonianPropagator"), a, new Formula.Negate(t), u, u));
        Formula infimum = Seq(Call(F.Id("inf"), Rel(t, FormulaRelationOperator.GreaterThan, D(0))), Sp, amplitude);
        Formula body = And(And(Rel(D(0), FormulaRelationOperator.LessThan, c),
            Rel(c, FormulaRelationOperator.LessThanOrEqual, D(1))), Equal(infimum, c));
        return Disp(Iff(Call(F.Id("SharplySedentary"), a, u, c), body));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula conclusion = Call(F.Id("SharplySedentary"), Call(F.Id("pathTwin"), n), D(0),
            new Formula.Fraction(D(1), n));
        Formula body = AllOf(n, Implies(Call(F.Id("Odd"), n),
            Implies(Rel(D(5), FormulaRelationOperator.LessThanOrEqual, n), conclusion)));
        return Disp(Iff(F.Id("claim"), body));
    }
}
