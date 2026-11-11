using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class CazenaveRandicSpectralBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/cazenave2026spectralgraphconjectures");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected graphs satisfy the Randic plus second-Laplacian spectral bound.",
        H("Cazenave's adjacency–Randić–Laplacian inequality"),
        Blocks(
            Node("adj-eig", "adjEig", "Ordered adjacency eigenvalues", EigenvalueFormula(),
                "Page 1 states: “A is the adjacency matrix, with eigenvalues λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ (counted with multiplicity) and rank rk(A).” The index i is zero based. The formula uses the ordinary adjacency matrix over Real and the decreasing eigenvalues₀. Here h is any proof that this matrix is Hermitian and e is any proof of the indicated cardinality equality; proof irrelevance identifies them with the proofs in the definition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("randic", "randic", "The Randić index", RandicFormula(),
                "Page 1 states: “R = ∑ᵤᵥ∈E (dᵤdᵥ)⁻¹ᐟ² is the Randić index.” The finite sum ranges over G.edgeFinset, so each unordered edge occurs once. Sym2.lift applies the symmetric reciprocal-square-root function to an unordered pair. The formula displays any symmetry proof s; proof irrelevance identifies it with the proof in the definition. Degrees are coerced from Nat to Real, and Real.sqrt is the nonnegative square root. Both endpoints of an edge have positive degree.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "Conjecture 4 (#112951)",
                Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Page 11 states: “Conjecture 4 (#112951). λ₁ ≤ R + µ₂.” Page 1 states: “All graphs are simple, undirected and connected, with n ≥ 2 vertices and m edges.” SimpleGraph supplies undirectedness and absence of loops. The parameter n in this formula is graph order minus two. The anonymous bracket supplies decidable adjacency. The ordinary Laplacian is D − A; LinWangCaiBroomSpectralRatio.lapEig G 1 is its second-largest eigenvalue, counted with multiplicity. At order two it is the smaller Laplacian eigenvalue.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", "The spectral inequality", ClaimBody(),
                "Choose u of maximum degree Δ and v of largest degree among the remaining vertices; write r = √Δ and d = degree(v). Connectedness gives Δ ≥ d ≥ 1. Edge charging gives r ≤ randic G. The positive vector taking value r at u and value one elsewhere satisfies A h ≤ (r + d − 1) h, so adjEig G 0 ≤ r + d − 1. A nonzero vector supported on u and v and orthogonal to the first Laplacian eigenvector has Rayleigh quotient at least d − 1. Expansion in the decreasing orthonormal spectral basis bounds that quotient above by lapEig G 1. The three estimates on this same graph give the displayed inequality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-cazenave2611c4"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("cazenave-randic-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Op(name) : new Formula.Apply(Op(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula App(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula DotName(Formula value, string name) => Seq(Parenthesized(value), Dot, Op(name));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => Seq(left, Plus, right);
    private static Formula FinN() => Call("Fin", V("n"));
    private static Formula GraphBinders(Formula size, Formula body) =>
        All("n", C("Nat"), All("G", Call("SimpleGraph", Call("Fin", size)),
            Seq(OpenBracket, Call("DecidableRel", DotName(V("G"), "Adj")), CloseBracket, Sp, body)));

    private static Formula EigenvalueFormula()
    {
        Formula matrix = App(DotName(V("G"), "adjMatrix"), C("Real"));
        Formula eig = Seq(V("h"), Dot, new Formula.Subscript(Op("eigenvalues"), D(0)));
        return GraphBinders(V("n"), All("i", FinN(),
            All("h", DotName(matrix, "IsHermitian"),
                All("e", Parenthesized(Eqn(V("n"), QCall("Fintype", "card", FinN()))),
                    Eqn(Call("adjEig", V("G"), V("i")),
                        App(eig, QCall("Fin", "cast", V("e"), V("i"))))))));
    }

    private static Formula Weight(Formula u, Formula v)
    {
        Formula degreeU = Parenthesized(Seq(App(DotName(V("G"), "degree"), u), Sp, Colon, Sp, C("Real")));
        Formula degreeV = Parenthesized(Seq(App(DotName(V("G"), "degree"), v), Sp, Colon, Sp, C("Real")));
        return new Formula.Fraction(D(1), QCall("Real", "sqrt", Parenthesized(Seq(degreeU, Sp, Cdot, Sp, degreeV))));
    }

    private static Formula RandicFormula()
    {
        Formula symmetry = All("u", FinN(), All("v", FinN(), Eqn(Weight(V("u"), V("v")), Weight(V("v"), V("u")))));
        Formula function = Seq(LambdaLower, Sp, Parenthesized(Seq(V("u"), Sp, V("v"), Sp, Colon, Sp, FinN())),
            Sp, Mapsto, Sp, Weight(V("u"), V("v")));
        Formula pair = Seq(Langle, Parenthesized(function), Comma, Sp, V("s"), Rangle);
        Formula sum = Seq(new Formula.Subscript(Sum,
                Seq(V("e"), Sp, InMacro, Sp, DotName(V("G"), "edgeFinset"))), Sp,
            QCall("Sym2", "lift", pair, V("e")));
        return GraphBinders(V("n"), All("s", Parenthesized(symmetry), Eqn(Call("randic", V("G")), sum)));
    }

    private static Formula ClaimBody()
    {
        Formula left = Call("adjEig", V("G"), D(0));
        Formula laplacian = QCall("LinWangCaiBroomSpectralRatio", "lapEig", V("G"), D(1));
        Formula inequality = LeqFormula(left, Add(Call("randic", V("G")), laplacian));
        return GraphBinders(Add(V("n"), D(2)), new Formula.Logic(
            DotName(V("G"), "Connected"), FormulaLogicOperator.Implies, inequality));
    }
}
