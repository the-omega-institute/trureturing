using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SignlessLaplacian;

internal sealed class LiGuoDegreeSequenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/liguo2025degreesequence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The triangle has signless Laplacian eigenvalues 4, 1, 1. Its truncated square sum is 4, exceeding the degree bound 3 in Li–Guo Conjecture 2.22.",
        H("The triangle refutes Li–Guo Conjecture 2.22"),
        Blocks(
            Node("TQ", "The truncated spectral square sum", SpectralSumFormula(),
                "Li and Guo, p. 4551: \"Let Q(G)=D(G)+A(G) be the signless Laplacian matrix of G and q₁(G)≥q₂(G)≥⋯≥qₙ(G) be the signless Laplacian eigenvalues of G.\" The graphSpectrum multiset of sourceMatrix G MatrixKind.signless contains every real eigenvalue with its multiplicity. The source sum on p. 4564 is over indices with qᵢ ≥ 2. Replacing its summand by max(q−2,0)² on all indices preserves the value, including q = 2. SimpleGraph (Fin n) describes a finite simple undirected loopless graph.",
                AssessedProvenance.FromLiterature(Source)),
            Node("R", "The degree bound", DegreeBoundFormula(),
                "Li and Guo, p. 4551: \"Let G be a graph with n vertices and m edges, and d₁(G)≥d₂(G)≥⋯≥dₙ(G) be the degree sequence of G.\" The factor d₁ in Conjecture 2.22 is SimpleGraph.maxDegree. The sum over vertices equals the sum over the decreasing degree sequence, since every vertex occurs once. Every degree is cast to ℝ before subtraction or division; subtraction is real subtraction.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 2.22", new Formula.Logic(Call("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())),
                "Li and Guo, Conjecture 2.22, p. 4564: \"Let G be a graph with degree sequence d₁≥d₂≥⋯≥dₙ. Then\" followed by ∑_{qᵢ≥2}(qᵢ−2)²≤(1−1/d₁)∑_{i=1}ⁿdᵢ(dᵢ−1). Here n ranges over ℕ and G over SimpleGraph (Fin n). The denominator 1/d₁ restricts the assertion to positive maximum degree. There is no connectedness or regularity restriction. TQ and R are the two displayed sides, and the spectral multiset counts repeated eigenvalues separately.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("liguo-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A triangle counterexample"), StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For SimpleGraph.cycleGraph 3 every degree and the maximum degree equal 2. The signless Laplacian is the real matrix [[2,1,1],[1,2,1],[1,1,2]], with characteristic polynomial (X−4)(X−1)(X−1). The Hermitian characteristic-root theorem gives the eigenvalue multiset {4,1,1}, retaining both copies of 1. Hence TQ = 4 and R = 3. Applying the asserted inequality to this positive-degree graph would give 4 ≤ 3. This proves the negation for the whole stated class; an infinite cycle-family formula is not asserted."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("li-guo-signless-laplacian"), ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("liguo-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Qualified(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(Qualified(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealCast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Reals()));
    private static Formula GraphBinders(Formula body) => All("n", Nats(), All("G", Call("SimpleGraph", Call("Fin", F.Id("n"))), body));

    private static Formula SpectralSumFormula()
    {
        var q = F.Id("q"); var g = F.Id("G");
        var summand = new Formula.Power(Call("max", Parenthesized(Sub(q, D(2))), D(0)), D(2));
        var function = Seq(F.Id("fun"), Sp, Parenthesized(Seq(q, Sp, Colon, Sp, Reals())), Sp, Mapsto, Sp, summand);
        var spectrum = Call("graphSpectrum", g, Call("MatrixKind.signless"));
        return GraphBinders(Equal(Call("TQ", g), Call("Multiset.sum", Call("Multiset.map", Parenthesized(function), spectrum))));
    }

    private static Formula DegreeBoundFormula()
    {
        var g = F.Id("G"); var i = F.Id("i");
        var degree = RealCast(Call("SimpleGraph.degree", g, i));
        var sum = Seq(F.Sum, Underscore, Grp(Seq(i, Sp, Colon, Sp, Call("Fin", F.Id("n")))), Sp,
            Mul(degree, Parenthesized(Sub(degree, D(1)))));
        var factor = Parenthesized(Sub(D(1), new Formula.Fraction(D(1), RealCast(Call("SimpleGraph.maxDegree", g)))));
        return GraphBinders(Equal(Call("R", g), Mul(factor, Parenthesized(sum))));
    }

    private static Formula ClaimBody()
    {
        var g = F.Id("G");
        var positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("SimpleGraph.maxDegree", g));
        var bound = new Formula.Relation(Call("TQ", g), FormulaRelationOperator.LessThanOrEqual, Call("R", g));
        return GraphBinders(new Formula.Logic(Parenthesized(positive), FormulaLogicOperator.Implies, bound));
    }
}
