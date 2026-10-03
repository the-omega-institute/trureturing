using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class AverageMixingTraceMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/godsil2023diagonal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n and every connected graph G on n vertices, the trace of the average mixing matrix of the adjacency quantum walk on G is at most that of the complete graph K_n. This proves Conjecture 9.1 of C. Godsil, K. Guo and M. Sobchuk (arXiv:1910.02039), read over connected graphs.",
        H("The complete graph maximizes the trace of the average mixing matrix"),
        Blocks(
            Node("idempotent", "The spectral idempotents", IdempotentFormula(),
                "For a simple graph G on the vertex set Fin n, with decidable adjacency, the adjacency matrix A(G) is a real symmetric matrix. "
                + "Let v_1, ..., v_n be the orthonormal eigenbasis of A(G) chosen by Mathlib (Matrix.IsHermitian.eigenvectorBasis), with eigenvalues lambda_1, ..., lambda_n (Matrix.IsHermitian.eigenvalues). "
                + "E_theta(G) is the sum of the outer products v_i v_i^T over the indices i with lambda_i = theta. "
                + "It is the orthogonal projection onto the theta-eigenspace of A(G), whatever orthonormal eigenbasis is chosen, and it is the zero matrix when theta is not an eigenvalue.",
                "idempotent", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("avgmixing", "The average mixing matrix", AvgMixingFormula(),
                "The paper writes A = sum_r theta_r E_r over the distinct eigenvalues theta_r and quotes Godsil (2013): the average mixing matrix is the sum over r of the Schur products E_r o E_r. "
                + "Here the sum runs over the set of eigenvalues {lambda_i : i in Fin n}, each distinct eigenvalue once, and o is the Schur (entrywise) product of matrices.",
                "avgMixing", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("avgmix-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 9.1"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(
                    Text("C. Godsil, K. Guo and M. Sobchuk, arXiv:1910.02039, Section 9 (Open problems), state after Table 2 and Corollary 6.3, as Conjecture 9.1 of the published version (Australas. J. Combin. 86(3) (2023)): \"The complete graph on "),
                    Math(F.Id("n")),
                    Text(" vertices attains the maximum trace with respect to the "),
                    Math(MHatA()),
                    Text(" for all "),
                    Math(F.Id("n")),
                    Text(".\" The maximum is read over connected graphs on n vertices, as in the 2026 restatement of A. Mohan, C. Tamon, Y. Xu and H. Zhan (arXiv:2608.20739); over all graphs the empty graph would have trace n. In the formula G ranges over the simple graphs on Fin n with decidable adjacency, Connected is SimpleGraph.Connected, and K_n is the complete graph, the top element of SimpleGraph (Fin n). Connected graphs are nonempty, so n is at least 1."))),
                DescribeRole.Definition),
            Node("result", "The complete graph attains the maximum", Disp(F.Id("claim")),
                "Fix a vertex a with a neighbour and an eigenvalue theta, and let q be the diagonal entry of E_theta at a. The column u = E_theta e_a satisfies A u = theta u, u_a = q and |u|^2 = q, so the coordinates of u off a have squared norm q - q^2. "
                + "Cauchy-Schwarz on the eigen-equation at a gives theta^2 q^2 <= (n - 1)(q - q^2). At a neighbour b of a, q = theta u_b minus the sum of u_c over the other neighbours c of b, a combination over deg(b) vertices other than a, so q^2 <= (theta^2 + n - 2)(q - q^2). "
                + "Eliminating theta gives (q^2 - (n - 1)(q - q^2))(q^2 + q - q^2) <= 0, hence q^2 <= (n - 1) q (1 - q) and n q <= n - 1. "
                + "The diagonal entries of the E_theta at a are nonnegative and sum to 1, and each is at most 1 - 1/n, so the sum of their squares, which is the diagonal entry of the average mixing matrix at a, is at most 1 - 2/n + 2/n^2. "
                + "In a connected graph with n >= 2 every vertex has a neighbour, so the trace is at most n - 2 + 2/n; for n = 1 the trace is 1. "
                + "For K_n with n >= 2, an eigenvector with eigenvalue other than -1 is constant with eigenvalue n - 1, and the trace of A(K_n) is 0, so exactly one eigenbasis vector has eigenvalue n - 1; hence the diagonal entries of E_(n-1) and E_(-1) are 1/n and 1 - 1/n, and the trace of the average mixing matrix of K_n is n - 2 + 2/n, as computed in the paper.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("godsil-2023-average-mixing-trace-maximum"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("avgmix-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula Leq(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula AllIn(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(F.Sum, Underscore, Grp(index), Sp, body);
    private static Formula Coord(Formula vector, Formula i) => new Formula.Subscript(vector, i);
    private static Formula Lambda(Formula i) => Coord(LambdaLower, i);
    private static Formula Spectrum() =>
        Seq(OpenBrace, Lambda(F.Id("i")), Sp, Colon, Sp, F.Id("i"), Sp, InMacro, Sp,
            Call(F.Id("Fin"), F.Id("n")), CloseBrace);
    private static Formula Idem(Formula graph, Formula theta) => Call(F.Id("idempotent"), graph, theta);
    private static Formula AvgMixing(Formula graph) => Call(F.Id("avgMixing"), graph);
    private static Formula Trace(Formula matrix) => Call(F.Id("trace"), matrix);
    private static Formula MHatA() => new Formula.Subscript(Seq(Widehat, Grp(F.Id("M"))), F.Id("A"));

    private static Formula IdempotentFormula()
    {
        Formula i = F.Id("i"), theta = Theta, v = Coord(F.Id("v"), i);
        Formula index = Seq(i, Colon, Sp, Lambda(i), Sp, Eq, Sp, theta);
        return Disp(Equal(Idem(F.Id("G"), theta),
            SumOver(index, Seq(v, Sp, new Formula.Power(v, F.Id("T"))))));
    }

    private static Formula AvgMixingFormula()
    {
        Formula theta = Theta, g = F.Id("G");
        Formula index = Seq(theta, Sp, InMacro, Sp, Spectrum());
        return Disp(Equal(AvgMixing(g),
            SumOver(index, Seq(Idem(g, theta), Sp, Circ, Sp, Idem(g, theta)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G");
        Formula graphs = Call(F.Id("SimpleGraph"), Call(F.Id("Fin"), n));
        Formula complete = new Formula.Subscript(F.Id("K"), n);
        Formula conclusion = Leq(Trace(AvgMixing(g)), Trace(AvgMixing(complete)));
        Formula body = AllIn(n, Seq(Mathbb, Grp(F.Id("N"))), AllIn(g, graphs,
            Implies(Call(F.Id("Connected"), g), conclusion)));
        return Disp(Iff(F.Id("claim"), body));
    }
}
