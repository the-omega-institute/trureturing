using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class EllipticSomborEnergyIntegerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/alikhanighanbaridehghanizadeh2024ellipticsombor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two four-cycles sharing a vertex have elliptic Sombor energy 144.",
        H("An integer elliptic Sombor energy"),
        Blocks(
            Node("ellipticSomborMatrix", "The elliptic Sombor matrix", MatrixFormula(),
                "Abstract, page 1: \"Let G be a simple graph with vertex set V(G) = {v₁, v₂, …, vₙ}. The elliptic Sombor matrix of G, denoted by A_ESO(G), is defined as the n×n matrix whose (i,j)-entry is (dᵢ+dⱼ)√(dᵢ²+dⱼ²) if vᵢ and vⱼ are adjacent and 0 for another cases.\" Vertices are labelled by Fin n, starting at zero. SimpleGraph.degree counts adjacent vertices. Typed val denotes the natural-number degree cast into ℝ before addition and squaring. Each entry is zero on a nonadjacent pair, including the diagonal.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("claim", "Conjecture 3.9", ClaimFormula(),
                "Conjecture 3.9, page 12: \"There is no graph with integer-valued elliptic Sombor energy.\" Abstract, page 1: \"The elliptic Sombor energy E_ESO of G is the sum of absolute values of the eigenvalues of A_ESO(G).\" Encoding: n is a natural number, G is any simple graph on Fin n, and adjacency is decidable. The matrix is always Hermitian because adjacency is symmetric. hA is a proof of that property and supplies Mathlib's eigenvalues, indexed by Fin n with algebraic multiplicity. The sum is independent of the choice of Hermitian proof. Every integer z is cast to ℝ; the claim excludes equality to all such casts. The empty graph is included in this literal all-graphs statement; the counterexample below has seven vertices and no isolated vertex.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("result", "Two squares with a common vertex", Disp(new Formula.Not(F.Id("claim"))),
                "Use the edges 0–1–2–3–0 and 0–4–5–6–0. Vertex zero has degree four and every other vertex has degree two. The four edges incident to zero have weight 12√5, and the other four have weight 8√2. An explicit invertible change of basis diagonalizes this real symmetric matrix with diagonal entries −56, −16, 0, 0, 0, 16, 56. Its characteristic polynomial is x³(x−56)(x+56)(x−16)(x+16). Mathlib's spectral theorem identifies the roots with the Hermitian eigenvalue multiset. The absolute values therefore sum to 144, an integer, so the conjecture is false.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alikhani-ghanbari-dehghanizadeh-2024-elliptic-sombor-energy-integer-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("esoint-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula CastReal(Formula value) =>
        Parenthesized(Seq(Call("val", value), Sp, Colon, Sp, Reals));
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula GraphBinders(Formula body) =>
        All("n", Nats, All("G", Call("SimpleGraph", Call("Fin", F.Id("n"))),
            Seq(OpenBracket, Call("DecidableRel", Call("Adj", F.Id("G"))),
                CloseBracket, Comma, Sp, body)));

    private static Formula MatrixFormula()
    {
        Formula g = F.Id("G"), i = F.Id("i"), j = F.Id("j");
        Formula di = CastReal(Call("degree", g, i)), dj = CastReal(Call("degree", g, j));
        Formula weight = Seq(Parenthesized(Seq(di, Sp, Plus, Sp, dj)), Sp, Cdot, Sp,
            Seq(Sqrt, Grp(new Formula.Power(di, D(2)), Sp, Plus, Sp,
                new Formula.Power(dj, D(2)))));
        Formula rhs = Seq(Left, OpenBrace, new Formula.Aligned([
            Seq(weight, Sp, Amp, Sp, F.Text, Grp(F.Id("if")), Sp, Call("Adj", g, i, j)),
            Seq(D(0), Sp, Amp, Sp, F.Text, Grp(F.Id("otherwise")))]), Right, Dot);
        return Disp(GraphBinders(All("i", Call("Fin", F.Id("n")),
            All("j", Call("Fin", F.Id("n")), Eq(Call("ellipticSomborMatrix", g, i, j), rhs)))));
    }

    private static Formula ClaimFormula()
    {
        Formula index = Seq(F.Id("i"), Sp, Colon, Sp, Call("Fin", F.Id("n")));
        Formula energy = Seq(new Formula.Subscript(Sum, index), Sp,
            Seq(Lvert, Sp, Call("eigenvalues", F.Id("hA"), F.Id("i")), Sp, Rvert));
        Formula differs = new Formula.Relation(energy, FormulaRelationOperator.NotEqual,
            CastReal(F.Id("z")));
        Formula body = GraphBinders(All("hA", Call("IsHermitian",
            Call("ellipticSomborMatrix", F.Id("G"))), All("z", Integers, differs)));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }
}
