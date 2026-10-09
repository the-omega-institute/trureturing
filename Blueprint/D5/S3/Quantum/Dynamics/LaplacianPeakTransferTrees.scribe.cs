using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class LaplacianPeakTransferTreesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/coutinho2025peak");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "There are arbitrarily large non-star trees with Laplacian peak state transfer. "
        + "For each positive odd s, join a root to s(s+1)+1 hubs and each hub to s(s+1) leaves. "
        + "Transfer from the root to every hub attains the spectral entry bound at time pi.",
        H("Infinitely many non-star trees admit Laplacian peak state transfer"),
        Blocks(
            Node("idempotent", "lapIdempotent", "Laplacian spectral idempotents", IdempotentFormula(),
                "Section 3, p. 5: \"E_r is the idempotent projection onto the θ_r-eigenspace.\" "
                + "The source writes M as the sum of θ_r E_r over its distinct eigenvalues. Here M is G.lapMatrix over the reals. "
                + "The formula sums the outer products of the real orthonormal eigenbasis vectors whose eigenvalue equals theta; "
                + "a missing eigenvalue gives the zero matrix. hL denotes G.isHermitian_lapMatrix over the reals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bounding", "boundingEntry", "An entry of the bounding matrix", BoundingFormula(),
                "Section 3, p. 5: \"We will refer to B(M) := ∑_{r=0}^d |(E_r)| as the bounding matrix of M, "
                + "as the (v,u)-entry of B(M) upper-bounds |U(t)_{v,u}| for all values of t.\" "
                + "Absolute values are entrywise. The finite image of hL.eigenvalues counts each distinct eigenvalue once. "
                + "The two arguments v,u specify the (v,u)-entry, and hL is G.isHermitian_lapMatrix over the reals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("propagator", "lapPropagator", "The Laplacian propagator", PropagatorFormula(),
                "Section 3, p. 5: \"In particular, the transition matrix of the continuous-time quantum walk on M "
                + "can be written as the following matrix-valued function in time:\" U(t) = e^{itM} = ∑_{r=0}^d e^{itθ_r} E_r. "
                + "For Laplacian dynamics M is G.lapMatrix over the reals, "
                + "mapped entrywise into the complex numbers by algebraMap. "
                + "ProjectionProbabilityFlow.hamiltonianPropagator at time -tau equals exp(i tau L), the source's propagator.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("peak", "PeakTransfer", "Peak state transfer", PeakFormula(),
                "Section 3, p. 5: \"For distinct vertices u,v, we say that there is peak state transfer from u to v "
                + "with respect to M if there exists a time τ such that |U(τ)_{v,u}| = B(M)_{v,u}.\" "
                + "Here tau encodes τ, M is the real Laplacian, and the complex norm is its absolute value. "
                + "The equality is at the (v,u)-entry, so u is the input vertex.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "Open Problem 7.1", ClaimFormula(),
                "Section 7, p. 21: \"Determine whether infinitely many such trees, not isomorphic to the star graph, "
                + "admit Laplacian peak state transfer.\" Figure 10, p. 22, shows two stars and the 10-vertex rooted tree with three hubs and two leaves per hub. "
                + "In the formula N ranges over natural lower bounds on the number n of vertices, T is a simple graph on Fin n, "
                + "and IsTree means connected and acyclic. The exclusion covers every star K_(1,m), including m=0, "
                + "through the absence of a SimpleGraph.Iso to completeBipartiteGraph (Fin 1) (Fin m). "
                + "The PeakTransfer instances use classical adjacency decidability. Arbitrarily large finite orders imply infinitely many isomorphism classes.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", "The answer is affirmative", Disp(F.Id("claim")),
                "Put l=s(s+1), k=l+1 and n=1+k(l+1), with s positive and odd. "
                + "The root, hubs and leaves give a subspace of cell-constant vectors preserved by the Laplacian. "
                + "The root basis vector decomposes into eigenvectors with eigenvalues 0, s^2+1 and (s+1)^2+1. "
                + "Their root-to-hub spectral entries have signs positive, positive and negative. "
                + "At time pi the corresponding phases are 1, 1 and -1, so the absolute value of the propagator entry equals "
                + "the sum of the absolute spectral entries. This is the phase-alignment mechanism of Lemma 5.2. "
                + "Each graph is connected and has n-1 edges. The root and a hub both have degree at least two, which excludes all stars. "
                + "Taking s=2N+1 yields a graph whose order is at least N. The resulting transfer is across one edge.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("lpst-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Dotted(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Member(string variable, string name) => Seq(F.Id(variable), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Graph(Formula n) => Call("SimpleGraph", Fin(n));
    private static Formula Lap() => Call(Member("G", "lapMatrix"), Real());
    private static Formula HermitianLet(Formula body) =>
        Seq(Named("let"), Sp, F.Id("hL"), Sp, Eq, Sp,
            Call(Seq(F.Id("G"), Dot, Operatorname, Grp(F.Id("isHermitian"), Underscore, Grp(F.Id("lapMatrix")))), Real()), Semi, Sp, body);
    private static Formula WithGraph(Formula body) => All("n", Nat(), All("G", Graph(F.Id("n")),
        Seq(OpenBracket, Call("DecidableRel", Member("G", "Adj")), CloseBracket, Comma, Sp, body)));
    private static Formula SumOver(Formula index, Formula body) => Seq(F.Sum, Underscore, Grp(index), Sp, body);
    private static Formula Eigenvalue(Formula i) => Call(Member("hL", "eigenvalues"), i);
    private static Formula Eigenvector(Formula i) =>
        Call(Member("hL", "eigenvectorBasis"), i);

    private static Formula IdempotentFormula()
    {
        Formula i = F.Id("i"), theta = F.Id("theta"), g = F.Id("G");
        Formula index = Seq(i, Colon, Sp, Fin(F.Id("n")), Comma, Sp, Eigenvalue(i), Sp, Eq, Sp, theta);
        Formula vector = Call(Dotted("WithLp", "ofLp"), Eigenvector(i));
        return Disp(WithGraph(All("theta", Real(), Eqn(Call("lapIdempotent", g, theta),
            HermitianLet(SumOver(index, Call("vecMulVec", vector, vector)))))));
    }

    private static Formula BoundingFormula()
    {
        Formula theta = F.Id("theta"), g = F.Id("G"), v = F.Id("v"), u = F.Id("u");
        Formula spectrum = Call(Dotted("Finset", "image"), Member("hL", "eigenvalues"), Named("univ"));
        Formula index = Seq(theta, Sp, InMacro, Sp, spectrum);
        return Disp(WithGraph(All("v", Fin(F.Id("n")), All("u", Fin(F.Id("n")),
            Eqn(Call("boundingEntry", g, v, u), HermitianLet(SumOver(index,
                new Formula.Absolute(Call("lapIdempotent", g, theta, v, u)))))))));
    }

    private static Formula PropagatorFormula()
    {
        Formula tau = F.Id("tau");
        Formula matrix = Call(Dotted("Matrix", "map"), Lap(), Call("algebraMap", Real(), Complex()));
        return Disp(WithGraph(All("tau", Real(), Eqn(Call("lapPropagator", F.Id("G"), tau),
            Call(Dotted("ProjectionProbabilityFlow", "hamiltonianPropagator"), matrix, Seq(Minus, tau))))));
    }

    private static Formula PeakFormula()
    {
        Formula g = F.Id("G"), u = F.Id("u"), v = F.Id("v"), tau = F.Id("tau");
        Formula distinct = new Formula.Relation(u, FormulaRelationOperator.NotEqual, v);
        Formula attains = Eqn(new Formula.Norm(Call("lapPropagator", g, tau, v, u)), Call("boundingEntry", g, v, u));
        return Disp(WithGraph(All("u", Fin(F.Id("n")), All("v", Fin(F.Id("n")),
            Iffn(Call("PeakTransfer", g, u, v), And(distinct, Ex("tau", Real(), attains)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), t = F.Id("T"), m = F.Id("m");
        Formula star = Call("completeBipartiteGraph", Fin(D(1)), Fin(m));
        Formula nonstar = All("m", Nat(), Call("IsEmpty", Call(Dotted("SimpleGraph", "Iso"), t, star)));
        Formula peak = Ex("u", Fin(n), Ex("v", Fin(n), Call("PeakTransfer", t, F.Id("u"), F.Id("v"))));
        Formula properties = And(Member("T", "IsTree"), And(nonstar, peak));
        Formula large = new Formula.Relation(n, FormulaRelationOperator.GreaterThanOrEqual, F.Id("N"));
        return Disp(Iffn(F.Id("claim"), All("N", Nat(), Ex("n", Nat(), And(large, Ex("T", Graph(n), properties))))));
    }
}
