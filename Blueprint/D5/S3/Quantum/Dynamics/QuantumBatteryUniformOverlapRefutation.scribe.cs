using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class QuantumBatteryUniformOverlapRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/sarkis2026starbattery");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A triangulated complete graph refutes the proposed star bound for the uniform overlap of the least adjacency eigenspace.",
        H("The star bound for the least-energy uniform overlap fails"), Blocks(
            Paragraph(Text(
                "The vertex set is Fin n, and G is a simple graph with decidable adjacency. "
                    + "The bracket denotes the instance argument for decidable adjacency; this argument is implicit in the matrix and overlap expressions. "
                    + "SimpleGraph.adjMatrix G real is the real adjacency matrix. Named objects retain their Lean namespaces.")),
            Node("lamMin", "The least adjacency eigenvalue", LamMinFormula(),
                "The real adjacency matrix is symmetric, hence Hermitian. The local hA is its Hermitian proof, obtained from SimpleGraph.isSymm_adjMatrix by Matrix.isHermitian_iff_isSymm. Matrix.IsHermitian.eigenvalues hA enumerates its real eigenvalues on Fin n. Their infimum in the real numbers defines lamMin, with every natural n included. For n greater than zero this is the least adjacency eigenvalue in the diagonalization of Section III.A, equation (11).",
                AssessedProvenance.FromLiterature(Source)),
            Node("wmin", "The overlap of the least eigenspace", WminFormula(),
                "Section III.A, equation (11), defines the mode weights as the squares of the inner products of the all-ones vector with the orthonormal adjacency eigenvectors. For a graph with at least one edge, N and its edge count M are positive, so E_k(h) = (N/M) epsilon_k + h in equation (14) is increasing in epsilon_k. Thus the minimizing modes in Section III.C are exactly the least-eigenvalue eigenvectors. D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum.idempotent G (lamMin G) is the orthogonal projection onto their eigenspace. Summing all its entries gives the squared norm of the projection of the all-ones vector, including every vector in a repeated least eigenspace.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1 on all graphs with an edge", ClaimFormula(),
                "Sarkis, Prosniak, Nigro and Tkatchenko, Section III.C, Conjecture 1, equation (24), propose the displayed inequality for every non-empty graph on n vertices. Non-empty means that the edge set has an element. Every natural n, every simple graph on Fin n, and every decidable adjacency are quantified. Observation 2, equation (23), gives the right-hand side as the least-energy uniform overlap of the star graph.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("quantum-battery-uniform-overlap-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A triangulated complete graph contradicts the bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take the q-triangulation of the complete graph on ten core vertices, with q = 27: "
                            + "for each of its 45 edges, add 27 vertices adjacent to precisely the two endpoints. "
                            + "The resulting graph has 10 + 27 times 45 = 1225 vertices and has an edge. "
                            + "Let A be its real adjacency matrix. The vector v with value 1 on each core vertex "
                            + "and -1/9 on each attached vertex satisfies A v = -18 v.")),
                    Paragraph(Text(
                        "For every real vector x on these vertices, completing squares at each attached vertex gives "
                            + "x^T (A + 18 I) x at least 5 times the sum of the squared core coordinates "
                            + "minus one half of the square of their sum. Cauchy-Schwarz makes this nonnegative. "
                            + "Hence every adjacency eigenvalue is at least -18, and v shows that -18 is the least eigenvalue.")),
                    Paragraph(Text(
                        "The sum of the coordinates of v is -125 and its squared norm is 25. "
                            + "Since v lies in the least eigenspace, Cauchy-Schwarz bounds its uniform overlap "
                            + "from below by (-125)^2/25 = 625. "
                            + "But 625 > 1225/2 - sqrt(1224), contradicting Conjecture 1."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sarkis-prosniak-nigro-tkatchenko-2026-uniform-overlap-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("quantum-battery-uniform-overlap-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula LamMinFormula()
    {
        Formula adjacency = At(Qualified("SimpleGraph", "adjMatrix"), X("G"), Reals());
        Formula hermitian = At(Qualified("Matrix", "IsHermitian"), adjacency);
        Formula proof = At(Qualified("Iff", "mpr"),
            Qualified("Matrix", "isHermitian_iff_isSymm"),
            At(Qualified("SimpleGraph", "isSymm_adjMatrix"), X("G")));
        Formula eigenvalue = At(Qualified("Matrix", "IsHermitian", "eigenvalues"), X("hA"), X("i"));
        return GraphParameters(Let("hA", hermitian, proof,
            Equal(LocalCall("lamMin", X("G")),
                At(Qualified("iInf"), LambdaOf("i", FinOf(X("n")), eigenvalue)))));
    }

    private static Formula WminFormula() => GraphParameters(Equal(LocalCall("wmin", X("G")),
        SumOver("i", FinOf(X("n")), SumOver("j", FinOf(X("n")),
            At(Qualified("D5", "S3", "Quantum", "Dynamics", "AverageMixingTraceMaximum", "idempotent"),
                X("G"), LocalCall("lamMin", X("G")), X("i"), X("j"))))));

    private static Formula ClaimFormula()
    {
        Formula edgeNonempty = At(Qualified("Set", "Nonempty"),
            At(Qualified("SimpleGraph", "edgeSet"), X("G")));
        Formula size = Typed(X("n"), Reals());
        Formula bound = Subtract(new Formula.Fraction(size, D(2)),
            At(Qualified("Real", "sqrt"), Subtract(size, D(1))));
        return Equivalence(Local("claim"), GraphParameters(Imp(edgeNonempty,
            new Formula.Relation(LocalCall("wmin", X("G")), FormulaRelationOperator.LessThanOrEqual, bound))));
    }

    private static Formula GraphParameters(Formula body) => All("n", Naturals(),
        All("G", At(Qualified("SimpleGraph"), FinOf(X("n"))),
            Seq(OpenBracket, At(Qualified("DecidableRel"), At(Qualified("SimpleGraph", "Adj"), X("G"))),
                CloseBracket, Comma, Sp, body)));
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Dynamics", "QuantumBatteryUniformOverlapRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            var words = part.Split('_');
            Formula name = X(words[0]);
            foreach (var word in words.Skip(1))
                name = Seq(Grp(name), Underscore, Grp(X(word)));
            items.Add(name);
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Operatorname, Grp(X("let")), Sp, Typed(X(name), type), Sp, Colon, Eq, Sp,
            Parenthesized(value), Semi, Sp, Parenthesized(body));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
