using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class SomborEnergyIntegerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/ghanbari2022somborenergy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The graph formed by three four-cycles sharing one vertex has Sombor spectrum 16, -16, 4, -4, 4, -4, 0, 0, 0, 0. Its Sombor energy is 48, refuting Conjecture 3.8 of Ghanbari.",
        H("An integer Sombor energy"),
        Blocks(
            Node("matrix", "The Sombor matrix", MatrixFormula(),
                "Abstract, page 1: \"Let G be a simple graph with vertex set V(G) = {v₁, v₂, …, vₙ}. The Sombor matrix of G, denoted by A_SO(G), is defined as the n×n matrix whose (i,j)-entry is √(dᵢ²+dⱼ²) if vᵢ and vⱼ are adjacent and 0 for another cases.\" Here G is Mathlib's SimpleGraph on Fin n, labelled 0 through n−1, Adj is its adjacency relation, and degree is SimpleGraph.degree, the number of adjacent vertices. The degrees are cast to real numbers before squaring. The formula gives each entry of somborMatrix G; its type is Matrix (Fin n) (Fin n) ℝ.",
                "somborMatrix", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 3.8", ClaimFormula(),
                "Conjecture 3.8, page 13: \"There is no graph with integer-valued Sombor energy.\" The Abstract, page 1, states: \"The Sombor energy En_SO of G is the sum of absolute values of the eigenvalues of A_SO(G).\" Section 1 specifies finite simple graphs without directed, multiple or weighted edges or self-loops. Every finite labelled graph is represented by SimpleGraph (Fin n). The Hermitian proof hA is constructed from symmetry of adjacency and of the sum of squared degrees; let hA in the formula denotes this proof, with its proof term implicit. Matrix.IsHermitian.eigenvalues lists the real eigenvalues with multiplicity. The sum ranges over all i : Fin n and is written inline. Comparing it to every integer z cast to ℝ expresses precisely nonintegrality. DecidableRel is an anonymous instance argument, not an extra restriction on a finite graph.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Three four-cycles sharing a vertex", Disp(new Formula.Not(F.Id("claim"))),
                "Take the cycles 0–1–2–3–0, 0–4–5–6–0 and 0–7–8–9–0. Vertex 0 has degree six; all other vertices have degree two. Thus the six central edges have weight a = √40 and the remaining six edges have weight b = √8. An explicit ten-column eigenvector matrix P has eigenvalues d = (16, -16, 4, -4, 4, -4, 0, 0, 0, 0) and satisfies PᵀP = diagonal(768, 768, 32, 32, 96, 96, 2, 2, 2, 128). Consequently Q = diagonal(768⁻¹, 768⁻¹, 32⁻¹, 32⁻¹, 96⁻¹, 96⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 128⁻¹)Pᵀ is its inverse. The identity somborMatrix G · P = P · diagonal d gives characteristic polynomial x⁴(x−16)(x+16)(x−4)²(x+4)². The Hermitian spectral theorem identifies its root multiset with the eigenvalue multiset. The absolute values sum to 48, contradicting claim at z = 48.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ghanbari-2022-sombor-energy-integer-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("soint-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(name switch {
            "Real.sqrt" => Seq(F.Id("Real"), Dot, F.Id("sqrt")),
            "Matrix.IsHermitian" => Seq(F.Id("Matrix"), Dot, F.Id("IsHermitian")),
            "Matrix.IsHermitian.eigenvalues" => Seq(F.Id("Matrix"), Dot, F.Id("IsHermitian"), Dot, F.Id("eigenvalues")),
            _ => F.Id(name)
        })), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(variable), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula GraphBinders(Formula body) =>
        All("n", Naturals(), All("G", Call("SimpleGraph", Fin(F.Id("n"))),
            Instance(Call("DecidableRel", Call("Adj", F.Id("G"))), body)));
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Reals()));

    private static Formula MatrixFormula()
    {
        Formula g = F.Id("G"), i = F.Id("i"), j = F.Id("j");
        Formula radicand = new Formula.Binary(
            new Formula.Power(Cast(Call("degree", g, i)), D(2)), FormulaBinaryOperator.Add,
            new Formula.Power(Cast(Call("degree", g, j)), D(2)));
        Formula root = Call("Real.sqrt", radicand);
        Formula rhs = Seq(Left, OpenBrace, new Formula.Aligned([
            Seq(root, Sp, Amp, Sp, F.Text, Grp(F.Id("if")), Sp, Call("Adj", g, i, j)),
            Seq(D(0), Sp, Amp, Sp, F.Text, Grp(F.Id("otherwise")))]), Right, Dot);
        return Disp(GraphBinders(All("i", Fin(F.Id("n")), All("j", Fin(F.Id("n")),
            Equal(Call("somborMatrix", g, i, j), rhs)))));
    }

    private static Formula ClaimFormula()
    {
        Formula h = F.Id("hA"), i = F.Id("i"), z = F.Id("z");
        Formula eigenvalue = Call("Matrix.IsHermitian.eigenvalues", h, i);
        Formula sum = Seq(F.Sum, Underscore, Grp(Seq(i, Sp, Colon, Sp, Fin(F.Id("n")))),
            Sp, new Formula.Absolute(eigenvalue));
        Formula inequality = new Formula.Relation(sum, FormulaRelationOperator.NotEqual, Cast(z));
        Formula body = Seq(F.Text, Grp(F.Id("let")), Sp, h, Sp, Colon, Sp,
            Call("Matrix.IsHermitian", Call("somborMatrix", F.Id("G"))), Comma, Sp,
            All("z", new Formula.Integers(), inequality));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(GraphBinders(body))));
    }
}
