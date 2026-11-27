using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class AlbrightMaxEdgeDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/albright2023kemenyedgederivative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized Laplacian edge derivative has sharp upper bound one.",
        H("The maximum normalized Laplacian edge derivative"),
        Blocks(
            Node("eigenspace", "Full normalized Laplacian eigenspace", EigenspaceFormula(),
                AssessedProvenance.FromRepo(Source),
                "At t = 0 the frozen one-pair perturbation is the ordinary unweighted adjacency. "
                + "The frozen normalized Laplacian acts on real Euclidean vertex space. "
                + "The eigenspace is the entire kernel of L(0) minus the given eigenvalue times the identity."),
            Node("rayleighAverage", "Normalized trace on the fixed eigenspace", RayleighFormula(),
                AssessedProvenance.FromRepo(Source),
                "For an orthonormal basis of the entire eigenspace with k elements, sum the fixed-vector Rayleigh forms "
                + "uᵀ L(t) u and divide by k. The vectors are fixed at t = 0. Compressing L(t) by orthogonal projection "
                + "onto this eigenspace identifies the sum with its trace at each t. In the formulas, ι is "
                + "the inclusion of the eigenspace into Euclidean space."),
            Node("edgeDerivative", "The derivative in Lemma 2.3", EdgeDerivativeFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Lemma 2.3, equation (2.3), averages over the k elements of an orthonormal basis for the eigenvalue λ. "
                + "For a single distinct pair x,y and a basis vector u, put s = 1 − λ and gᵢ = uᵢ/√dᵢ. "
                + "The summand is s(gₓ² + gᵧ²) − 2gₓgᵧ. For positive degrees this equals the source expression "
                + "with denominators dₓ, dᵧ and √(dₓdᵧ). The same definition covers edges and nonedges."),
            Node("claim", "Conjecture 2.20", ClaimFormula(showDefinition: true),
                AssessedProvenance.FromLiterature(Source),
                "Conjecture 2.20 states that over all graphs the maximum edge derivative for any pair of vertices is 1. "
                + "The universal clause ranges over every finite connected simple unweighted graph of order at least two, "
                + "every distinct pair, and every real normalized Laplacian eigenvalue of positive multiplicity. "
                + "The basis has type OrthonormalBasis on the full eigenspace, so k is its dimension. "
                + "For each such basis, the source formula is the derivative of the normalized compressed trace at zero, "
                + "is basis-independent and is at most 1. The attaining graph is the connected path on three vertices, "
                + "with the nonedge joining its endpoints and the one-dimensional eigenspace at eigenvalue 1. "
                + "Write P₃ for pathGraph 3. R and D denote rayleighAverage and edgeDerivative, with the graph, pair "
                + "and eigenvalue given by subscripts. Derivative at zero is the two-sided HasDerivAt predicate."),
            Describe.Lean(DescribeId.Create("albright-max-edge-derivative-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The attained maximum is one"),
                StatementSource.FromAuthor(Disp(ClaimFormula(showDefinition: false))), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("This proves Conjecture 2.20 of Albright et al. using the derivative in Lemma 2.3. "
                        + "The perturbation adds t to the two opposite adjacency entries. The degree row sums "
                        + "increase by t at each endpoint. Write P = D⁻¹ᐟ² and B = PAP at zero. Differentiating each "
                        + "reciprocal square root gives L′ = (HB + BH)/2 − PCP, where C is the perturbation matrix "
                        + "and H has diagonal dᵢ′/dᵢ. On an s-eigenvector of B, the resulting quadratic form is "
                        + "the Lemma 2.3 summand. The trace identity and derivative uniqueness give independence of basis.")),
                    Paragraph(Text("The ordinary graph Laplacian and the sum of squares over ordered adjacent pairs give "
                        + "the inequalities for I − B and I + B. Thus −1 ≤ s ≤ 1. Completing a square bounds the "
                        + "summand by (1 + s)(gₓ² + gᵧ²). If s ≤ 0, degrees are at least one and the endpoint mass "
                        + "is at most one. For s > 0 and adjacent endpoints with degrees at least two, the scaled "
                        + "endpoint mass is at most one half. At a leaf on an adjacent pair, the eigenvector "
                        + "equation gives gᵧ = s gₓ after labelling the leaf x, and the summand is nonpositive.")),
                    Paragraph(Text("For a nonedge let w be u restricted to x and y, and let m = uₓ² + uᵧ². "
                        + "Then wᵀBw = 0 and wᵀu = wᵀw = m. Evaluating the quadratic form of I + B on w − mu "
                        + "gives m − (1 + s)m² ≥ 0. With m > 0 this yields (1 + s)m ≤ 1. The case m = 0 gives "
                        + "a zero summand. Every basis vector therefore contributes at most one, so the average "
                        + "has the same bound for every positive multiplicity.")),
                    Paragraph(Text("For the path on three vertices, the unit vector (1,0,−1)/√2 spans the "
                        + "eigenspace at 1. The perturbed normalized Laplacian on this vector has eigenvalue "
                        + "1 + t/(1 + t) near zero. Its derivative at zero is 1."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("albright-et-al-2023-max-edge-derivative-conjecture-2-20"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("albright-max-edge-derivative-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Lam => LambdaLower;
    private static Formula Path => new Formula.Subscript(V("P"), D(3));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) : Apply(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name))), args);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Typed(Formula name, Formula type) => Seq(name, Colon, Sp, type);
    private static Formula Indices(Formula graph, Formula x, Formula y, Formula eigenvalue) =>
        Seq(graph, Comma, x, Comma, y, Comma, eigenvalue);
    private static Formula Eigenspace(Formula graph, Formula x, Formula y, Formula eigenvalue) =>
        Call("eigenspace", graph, x, y, eigenvalue);
    private static Formula Basis(Formula k, Formula eigenspace) =>
        Call("OrthonormalBasis", Fin(k), Real, eigenspace);
    private static Formula Laplacian(Formula t) =>
        Call("normLap", Call("paramAdj", V("G"), V("x"), V("y"), t));
    private static Formula GraphParameters() =>
        Seq(Forall, Sp, Typed(V("n"), Nat), Comma, Sp,
            Typed(V("G"), Call("SimpleGraph", Fin(V("n")))), Sp,
            OpenBracket, Call("DecidableRel", Seq(V("G"), Dot, V("Adj"))), CloseBracket, Comma);
    private static Formula PairAndEigenvalue() =>
        Seq(Forall, Sp, Typed(Seq(V("x"), Sp, V("y")), Fin(V("n"))), Comma, Sp,
            Typed(Lam, Real), Comma);
    private static Formula BasisParameters() =>
        Seq(Forall, Sp, Typed(V("k"), Nat), Comma, Sp,
            Typed(V("b"), Basis(V("k"), Eigenspace(V("G"), V("x"), V("y"), Lam))), Comma);
    private static Formula BasisCoordinates(Formula u) =>
        Seq(u, Sp, Colon, Eq, Sp,
            Qualified("WithLp", "ofLp", Apply(Iota, Apply(V("b"), V("i")))), Quad,
            Open, Typed(V("i"), Fin(V("k"))), Close, Comma);

    private static Formula EigenspaceFormula() => new Formula.Aligned([
        Seq(Amp, GraphParameters(), Quad, PairAndEigenvalue()),
        Seq(Amp, Eigenspace(V("G"), V("x"), V("y"), Lam), Sp, Eq, Sp, Ker, Open,
            Call("toEuclideanLin", Laplacian(D(0))), Sp, Minus, Sp, Lam, Sp, Cdot, Sp, V("I"), Close)
    ]);

    private static Formula RayleighFormula()
    {
        Formula u = new Formula.Subscript(V("u"), V("i"));
        Formula sum = Seq(new Formula.Subscript(Sum, Typed(V("i"), Fin(V("k")))), Sp,
            Langle, Sp, u, Comma, Sp, Laplacian(V("t")), Sp, u, Sp, Rangle);
        return new Formula.Aligned([
            Seq(Amp, GraphParameters(), Quad, PairAndEigenvalue()),
            Seq(Amp, BasisParameters(), Quad, Forall, Sp, Typed(V("t"), Real), Comma),
            Seq(Amp, BasisCoordinates(u)),
            Seq(Amp, Call("rayleighAverage", V("G"), V("x"), V("y"), Lam, V("b"), V("t")), Sp,
                Eq, Sp, new Formula.Fraction(sum, V("k")))
        ]);
    }

    private static Formula EdgeDerivativeFormula()
    {
        Formula u = new Formula.Subscript(V("u"), V("i"));
        Formula Scaled(string vertex) => new Formula.Fraction(Apply(u, V(vertex)),
            Seq(Sqrt, Grp(Apply(Seq(V("G"), Dot, V("degree")), V(vertex)))));
        Formula gx = Scaled("x");
        Formula gy = Scaled("y");
        Formula summand = Seq(OpenBracket, Open, D(1), Minus, Lam, Close, Open,
            new Formula.Power(gx, D(2)), Plus, new Formula.Power(gy, D(2)), Close,
            Minus, D(2), Cdot, gx, Cdot, gy, CloseBracket);
        Formula sum = Seq(new Formula.Subscript(Sum, Typed(V("i"), Fin(V("k")))), Sp, summand);
        return new Formula.Aligned([
            Seq(Amp, GraphParameters(), Quad, PairAndEigenvalue()),
            Seq(Amp, BasisParameters()),
            Seq(Amp, BasisCoordinates(u)),
            Seq(Amp, Call("edgeDerivative", V("G"), V("x"), V("y"), Lam, V("b")), Sp,
                Eq, Sp, new Formula.Fraction(sum, V("k")))
        ]);
    }

    private static Formula ClaimFormula(bool showDefinition)
    {
        Formula connected = Seq(V("G"), Dot, V("Connected"));
        Formula eigenspace = Eigenspace(V("G"), V("x"), V("y"), Lam);
        Formula witnessSpace = Eigenspace(Path, D(0), D(2), D(1));
        Formula general = Indices(V("G"), V("x"), V("y"), Lam);
        Formula witness = Indices(Path, D(0), D(2), D(1));
        Formula DerivativeFunction(Formula index) => new Formula.Subscript(V("D"), index);
        Formula RayleighFunction(Formula index) => new Formula.Subscript(V("R"), index);
        Formula db = Apply(DerivativeFunction(general), V("b"));
        Formula hypotheses = Seq(Open, GraphParameters(), Sp, D(2), Leq, Sp, V("n"), Sp, Rightarrow, Sp,
            connected, Sp, Rightarrow);
        return new Formula.Aligned([
            showDefinition ? Seq(Amp, Call("claim"), Sp, Colon, Eq, Sp, hypotheses) : Seq(Amp, hypotheses),
            Seq(Amp, Quad, Forall, Sp, Typed(Seq(V("x"), Sp, V("y")), Fin(V("n"))), Comma, Sp,
                V("x"), Sp, Neq, Sp, V("y"), Sp, Rightarrow, Sp, Forall, Sp, Typed(Lam, Real), Comma, Sp,
                Forall, Sp, Typed(V("k"), Nat), Comma, Sp, D(0), Lt, V("k"), Sp, Rightarrow),
            Seq(Amp, Quad, Forall, Sp, Typed(V("b"), Basis(V("k"), eigenspace)), Comma, Sp,
                Call("HasDerivAt", Apply(RayleighFunction(general), V("b")), db, D(0)), Sp, Land),
            Seq(Amp, Quad, Sp, db, Sp, Leq, Sp, D(1), Sp, Land, Sp,
                Open, Forall, Sp, Typed(V("c"), Basis(V("k"), eigenspace)), Comma, Sp, db, Eq,
                Apply(DerivativeFunction(general), V("c")), Close, Close),
            Seq(Amp, Land, Sp, Seq(Path, Dot, V("Connected")), Sp, Land, Sp,
                Open, Typed(D(0), Fin(D(3))), Close, Neq, D(2), Sp, Land, Sp,
                Neg, Sp, Apply(Seq(Path, Dot, V("Adj")), D(0), D(2)), Sp, Land, Sp,
                Call("finrank", Real, witnessSpace), Eq, D(1)),
            Seq(Amp, Land, Sp, Open, Exists, Sp, Typed(V("b"), Basis(D(1), witnessSpace)), Comma, Sp,
                Call("HasDerivAt", Apply(RayleighFunction(witness), V("b")), D(1), D(0)), Sp, Land, Sp,
                Apply(DerivativeFunction(witness), V("b")), Eq, D(1), Close)
        ]);
    }
}
