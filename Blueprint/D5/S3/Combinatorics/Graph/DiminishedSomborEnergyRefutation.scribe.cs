using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DiminishedSomborEnergyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/movahedi2025diminishedsombor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The edgeless graph has zero diminished Sombor matrix, zero eigenvalues and zero energy. Since zero is an integer, it refutes Movahedi's Conjecture 5.1.",
        H("Zero energy of the edgeless graph"),
        Blocks(
            Node("matrix", "The diminished Sombor matrix", MatrixFormula(),
                "Page 2: \"Motivated by this newly introduced index, and following on the approach in [5, 28], we introduce the diminished Sombor matrix for the graph G, denoted by ℳ = M_DS(G) = (μ_ij), of order n as follows\". The displayed entry is sqrt(d_i² + d_j²)/(d_i + d_j) on edges and zero otherwise. SimpleGraph.degree supplies the vertex degrees, explicitly cast from natural numbers to real numbers before squaring, addition and division. ite is Lean's if-then-else. Vertices are Fin n, labelled 0 through n−1; relabelling the source's 1 through n does not change the spectrum. On an edge both degrees are positive, so its denominator is positive. On a non-edge the zero branch applies, with no quotient evaluated.",
                "diminishedSomborMatrix", AssessedProvenance.FromLiterature(Source)),
            Node("energy", "The diminished Sombor energy", EnergyFormula(),
                "Page 2: \"We define the diminished Sombor energy as follows\", followed by E_DSO(G) = ∑_{i=1}^n |λ_i|. The source's eigenvalues are real and counted with multiplicity. The real matrix is symmetric because adjacency is symmetric and both degree sums are symmetric. The definition proves this Hermitian property locally and uses Mathlib's Matrix.IsHermitian.eigenvalues, indexed by Fin n. In the formula h is any proof of that same Hermitian property; proof irrelevance makes its choice immaterial. This proof binder exposes the local proof argument of the spectral function, not an additional graph hypothesis. The sum is over all n eigenvalues, with multiplicity, and its order does not affect the energy.",
                "diminishedSomborEnergy", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 5.1", ClaimFormula(),
                "Section 5, page 19: \"There does not exist a graph whose diminished Sombor energy is an integer value.\" The encoding quantifies over positive orders n and all simple graphs on Fin n with decidable adjacency. An integer value means equality in the reals with the cast of some z : ℤ. No edge or connectedness condition appears in the conjecture. The paper itself includes edgeless graphs in the equality case of its upper energy bound.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("dse-result"), DeclarationHandle.Create(Prefix + "result"),
                H("An integer energy counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take the edgeless graph on Fin 1. Every matrix entry is zero by the non-edge branch. Mathlib's Hermitian spectral theorem identifies a zero matrix with an identically zero eigenvalue function, so the energy is zero. Choosing the integer zero contradicts the conjecture. This argument concerns the literal all-graphs statement; nonintegrality for graphs with at least one edge remains open."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("movahedi-2025-diminished-sombor-energy-integer"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("dse-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula Matrix(Formula g) => Call("diminishedSomborMatrix", g);
    private static Formula Energy(Formula g) => Call("diminishedSomborEnergy", g);
    private static Formula CastReal(Formula value) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, Reals()));
    private static Formula Degree(Formula g, Formula i) =>
        CastReal(new Formula.Apply(Qualified("SimpleGraph", "degree"), [g, i]));
    private static Formula GraphBinders(Formula body) =>
        All("n", Naturals(), All("G", Call("SimpleGraph", Call("Fin", F.Id("n"))),
            Instance(Call("DecidableRel", Call("Adj", F.Id("G"))), body)));

    private static Formula MatrixFormula()
    {
        Formula g = F.Id("G"), i = F.Id("i"), j = F.Id("j");
        Formula di = Degree(g, i), dj = Degree(g, j);
        Formula numerator = new Formula.Apply(Qualified("Real", "sqrt"),
            [Add(new Formula.Power(di, D(2)), new Formula.Power(dj, D(2)))]);
        Formula quotient = new Formula.Fraction(numerator, Add(di, dj));
        Formula entry = new Formula.Apply(Matrix(g), [i, j]);
        Formula body = Equal(entry, Call("ite", Call("Adj", g, i, j), quotient, D(0)));
        return Disp(GraphBinders(All("i", Call("Fin", F.Id("n")),
            All("j", Call("Fin", F.Id("n")), body))));
    }

    private static Formula EnergyFormula()
    {
        Formula g = F.Id("G"), h = F.Id("h"), i = F.Id("i");
        Formula eigenvalues = Seq(Operatorname, Grp(Seq(F.Id("Matrix"), Dot,
            F.Id("IsHermitian"), Dot, F.Id("eigenvalues"))));
        Formula eigenvalue = new Formula.Apply(eigenvalues, [h, i]);
        Formula sum = Seq(Sum, Underscore, Grp(Seq(i, Sp, Colon, Sp,
            Call("Fin", F.Id("n")))), Sp, new Formula.Absolute(eigenvalue));
        return Disp(GraphBinders(All("h",
            new Formula.Apply(Qualified("Matrix", "IsHermitian"), [Matrix(g)]),
            Equal(Energy(g), sum))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), z = F.Id("z");
        Formula integerValue = Seq(Exists, Sp, Parenthesized(Seq(z, Sp, Colon, Sp, Integers())),
            Comma, Sp, Equal(Energy(g), CastReal(z)));
        Formula graphClause = All("G", Call("SimpleGraph", Call("Fin", n)),
            Instance(Call("DecidableRel", Call("Adj", g)),
                new Formula.Not(Parenthesized(integerValue))));
        Formula positive = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);
        Formula quantified = All("n", Naturals(), new Formula.Logic(Parenthesized(positive),
            FormulaLogicOperator.Implies, Parenthesized(graphClause)));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(quantified)));
    }
}
