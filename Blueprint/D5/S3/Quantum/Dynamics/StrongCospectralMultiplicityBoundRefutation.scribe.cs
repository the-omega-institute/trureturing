using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class StrongCospectralMultiplicityBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/monterde2022strongcospectralitytwins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The connected graph K_{2,3} has two pairwise strongly cospectral vertices and an adjacency eigenspace of dimension at least three, contradicting the proposed multiplicity bound.",
        H("Strong cospectrality does not satisfy the general multiplicity bound"),
        Blocks(
            Definition("StronglyCospectral", "Strong cospectrality for adjacency",
                StronglyCospectralFormula(), AssessedProvenance.FromLiterature(Source),
                "For a simple graph G on Fin n with decidable adjacency, idempotent G θ is the real orthogonal projection onto the θ-eigenspace of its adjacency matrix. "
                    + "The vertices u and v are strongly cospectral when their projected coordinate vectors differ, at each real θ, by a real scalar c of absolute value one. "
                    + "This is the real symmetric case of the source's definition in arXiv v2 TeX, lines 170–192. "
                    + "The coordinate vector at u is Pi.single u 1. For a real number outside the spectrum the projection is zero, so quantifying over all real θ adds no restriction. "
                    + "The definition permits u and v to be equal."),
            Definition("maxMultiplicity", "The largest adjacency eigenvalue multiplicity",
                MaxMultiplicityFormula(), AssessedProvenance.FromLiterature(Source),
                "Take the natural-valued supremum of the real dimensions of the adjacency eigenspaces, over all real θ. "
                    + "Every such dimension is at most n, and a number outside the spectrum contributes zero. "
                    + "For a nonempty vertex set this is the largest eigenvalue multiplicity used in arXiv v2 TeX, line 727; the definition also gives zero for the empty graph. "
                    + "Matrix.mulVecLin is the linear map induced by the real adjacency matrix. Its eigenspace is viewed as the subtype of real coordinate vectors that belong to it."),
            Definition("claim", "The extension to connected simple graphs",
                ClaimFormula(), AssessedProvenance.FromRepo(Source),
                "In arXiv v2 TeX, line 727, Monterde recalls the bound for normal Cayley graphs and asks whether it extends to other graph classes and generalized adjacency matrices. "
                    + "Here the assertion is that every connected simple graph G on n vertices and every finite set S of pairwise adjacency strongly cospectral vertices satisfy |S| ≤ n/maxMultiplicity G. "
                    + "Ordinary adjacency is the case α = β = 0 and γ = 1 of the generalized adjacency matrix in lines 143–150 and 161. "
                    + "Pairwise strong cospectrality includes equal vertices. The cardinality of S, n and maxMultiplicity G are each cast from the natural numbers to the reals before comparison and division."),
            Describe.Lean(
                DescribeId.Create("strong-cospectral-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A counterexample on five vertices"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let G = K_{2,3} have parts {0,1} and {2,3,4}, and write A for its real adjacency matrix. "
                            + "The real linear map f sends x = (x₀,x₁,x₂) to (x₀,−x₀,x₁+x₂,−x₁,−x₂). "
                            + "The sum of the coordinates on each part is zero, so A f(x) = 0. "
                            + "Coordinates 1, 3 and 4 recover −x₀, −x₁ and −x₂, making f injective into the zero eigenspace. "
                            + "That eigenspace therefore has dimension at least three. Every eigenspace has dimension at most five, so the defining supremum is bounded and m = maxMultiplicity G is at least three.")),
                    Paragraph(Text(
                        "Set Q = A²/3 − I and let e₀ and e₁ be the coordinate vectors at 0 and 1. "
                            + "Direct multiplication gives Q e₀ = e₁ and A³ = 6A. "
                            + "If A v = θv for a nonzero real vector v, the cubic identity gives θ(θ²−6) = 0, hence θ = 0 or θ² = 6. "
                            + "For every vector with A v = θv, evaluation of the quadratic expression gives Q v = (θ²/3−1)v.")),
                    Paragraph(Text(
                        "Write c = θ²/3−1. The matrix Q is symmetric. For an orthonormal adjacency eigenbasis vector w of eigenvalue θ, "
                            + "taking the inner product of w with Q e₀ = e₁ and moving Q to w gives w₁ = c w₀. "
                            + "The projection Eθ is the sum of w wᵀ over the basis vectors with eigenvalue θ. "
                            + "The coordinate identity thus yields Eθ e₁ = c Eθ e₀.")),
                    Paragraph(Text(
                        "When θ occurs in the eigenbasis, its basis vector is nonzero, so θ = 0 or θ² = 6. "
                            + "Accordingly c is −1 or 1, has absolute value one and satisfies c² = 1. "
                            + "Substituting Eθ e₁ = c Eθ e₀ then gives Eθ e₀ = c Eθ e₁, the required orientation of strong cospectrality. "
                            + "When θ does not occur, Eθ is an empty sum and is zero; the scalar 1 suffices. "
                            + "For each equal pair in S = {0,1}, use the scalar 1. For the pair (0,1), use the relation just proved. "
                            + "For the reversed pair, a real scalar of absolute value one has square one, so the same scalar reverses the relation. "
                            + "Thus every ordered pair in S is strongly cospectral.")),
                    Paragraph(Text(
                        "Both parts of G are nonempty, so G is connected. Apply the asserted bound with n = 5 and S = {0,1}, whose cardinality is two. "
                            + "It gives 2 ≤ 5/m. Since m ≥ 3, its real cast is positive; multiplying by it gives 2m ≤ 5, while m ≥ 3 gives 2m ≥ 6. "
                            + "This contradiction refutes the asserted extension."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("monterde-2022-strong-cospectral-multiplicity-bound-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("strong-cospectral-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula StronglyCospectralFormula()
    {
        Formula condition = All("θ", Reals(), Some("c", Reals(),
            Conjunction(Equal(new Formula.Absolute(X("c")), Typed(D(1), Reals())),
                Equal(ProjectedCoordinate(X("u")), Smul(X("c"), ProjectedCoordinate(X("v")))))));
        return GraphBinders(All("u", FinOf(X("n")), All("v", FinOf(X("n")),
            Equivalence(LocalCall("StronglyCospectral", X("G"), X("u"), X("v")), condition))));
    }

    private static Formula MaxMultiplicityFormula()
    {
        Formula adjacency = At(Qualified("SimpleGraph", "adjMatrix"), Reals(), X("G"));
        Formula eigenspace = At(Qualified("Module", "End", "eigenspace"),
            At(Qualified("Matrix", "mulVecLin"), adjacency), X("θ"));
        Formula vectors = At(Qualified("Subtype"),
            LambdaOf("x", Arrow(FinOf(X("n")), Reals()), Member(X("x"), eigenspace)));
        Formula dimension = At(Qualified("Module", "finrank"), Reals(), vectors);
        Formula supremum = At(Qualified("sSup"), At(Qualified("Set", "range"),
            LambdaOf("θ", Reals(), dimension)));
        return GraphBinders(Equal(Typed(LocalCall("maxMultiplicity", X("G")), Naturals()), supremum));
    }

    private static Formula ClaimFormula()
    {
        Formula relation = LocalCall("StronglyCospectral", X("G"), X("u"), X("v"));
        Formula pairwise = All("u", FinOf(X("n")), Arrow(Member(X("u"), X("S")),
            All("v", FinOf(X("n")), Arrow(Member(X("v"), X("S")), relation))));
        Formula inequality = new Formula.Relation(
            RealCast(At(Qualified("Finset", "card"), X("S"))),
            FormulaRelationOperator.LessThanOrEqual,
            new Formula.Fraction(RealCast(X("n")), RealCast(LocalCall("maxMultiplicity", X("G")))));
        Formula body = GraphBinders(Arrow(At(Qualified("SimpleGraph", "Connected"), X("G")),
            All("S", At(Qualified("Finset"), FinOf(X("n"))), Arrow(pairwise, inequality))));
        return Equivalence(Local("claim"), body);
    }

    private static Formula ProjectedCoordinate(Formula vertex) => At(Qualified("Matrix", "mulVec"),
        At(Qualified("D5", "S3", "Quantum", "Dynamics", "AverageMixingTraceMaximum", "idempotent"),
            X("G"), X("θ")),
        At(Qualified("Pi", "single"), vertex, Typed(D(1), Reals())));
    private static Formula GraphBinders(Formula body) => All("n", Naturals(),
        All("G", At(Qualified("SimpleGraph"), FinOf(X("n"))), Seq(OpenBracket,
            At(Qualified("DecidableRel"), At(Qualified("SimpleGraph", "Adj"), X("G"))),
            CloseBracket, Comma, Sp, Parenthesized(body))));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Dynamics",
        "StrongCospectralMultiplicityBoundRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => name == "θ" ? Theta : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula RealCast(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
