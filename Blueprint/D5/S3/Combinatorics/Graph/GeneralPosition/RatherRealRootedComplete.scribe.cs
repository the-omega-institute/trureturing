using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.GeneralPosition;

internal sealed class RatherRealRootedCompleteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/rather2026generalposition");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite nonempty connected graph has a real-rooted general position polynomial exactly when it is complete.",
        H("Real-rooted general position polynomials"),
        Blocks(
            Paragraph(Text("Vertices form a finite type V. General position uses IsGeneralPosition from CylinderSevenTen: no three distinct selected vertices satisfy the distance equality through the middle vertex. Distances are SimpleGraph.dist. On connected graphs these are shortest-path distances; no classification of disconnected graphs is asserted.")),
            Node("counts", "Counting general position sets", "alpha", DescribeRole.Definition,
                GraphParameters(All("k", Nat(), Eq(Call("alpha", X("G"), X("k")), AlphaBody()))),
                AssessedProvenance.FromLiterature(Source),
                "Section 2, PDF page 4: “For each k ≥ 0, let α_k(G) denote the number of general position sets of size k.” Finset.univ ranges over all finite subsets of V; the filter requires both cardinality k and general position. Each subset is counted once."),
            Node("polynomial", "The general position polynomial", "psi", DescribeRole.Definition,
                GraphParameters(Eq(Call("psi", X("G")), PsiBody())),
                AssessedProvenance.FromLiterature(Source),
                "Section 2, PDF page 4: “The general position polynomial of G is ψ(G) = ∑_{k≥0} α_k(G)x^k.” The indeterminate is Polynomial.X and coefficients are integers. The sum uses Finset.range (Fintype.card V + 1), since no subset has more than Fintype.card V vertices. Polynomial.C embeds the natural count after its cast to Int."),
            Node("real-roots", "Only real complex zeros", "IsRealRooted", DescribeRole.Definition,
                GraphParameters(Eq(Call("IsRealRooted", X("G")), Parenthesized(RealRootedBody()))),
                AssessedProvenance.FromLiterature(Source),
                "Section 8, item 1, PDF page 29: “For no nontrivial family is it currently known whether ψ(G) is always real-rooted.” Real-rooted means that every complex zero of psi G has zero imaginary part. Polynomial.aeval maps the integer coefficients into Complex."),
            Node("claim", "The connected classification", "claim", DescribeRole.Definition,
                Eq(X("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                "Section 8, item 1, PDF page 29: “For no nontrivial family is it currently known whether ψ(G) is always real-rooted. Even partial real-rootedness results for chordal graphs, bipartite graphs, or claw-free graphs (in analogy with [8, 13]) would be significant.” Section 1, PDF page 1: “All graphs considered are finite, simple and undirected.” The statement classifies all finite nonempty connected simple graphs: real-rootedness is equivalent to equality with the complete graph, SimpleGraph top."),
            Node("result", "Real-rootedness is equivalent to completeness", "result", DescribeRole.Theorem,
                ClaimBody(), AssessedProvenance.FromRepo(Source),
                "Every subset with at most two vertices is in general position, so the first three coefficients are 1, n and choose(n,2), where n is the vertex count. Reflecting the polynomial at n gives a monic real-split polynomial. If zero were a root, removing it would preserve the first two elementary symmetric functions on only n−1 roots, contradicting Newton's inequality. Thus the full vertex set is in general position. In a connected noncomplete graph a shortest path contains a distance-two triple, which contradicts that property. Conversely, all subsets of a complete graph are in general position, giving psi top = (1 + Polynomial.X)^n and only the zero −1.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rather-2026-general-position-real-rooted-complete"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name))));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula GraphParameters(Formula body, bool decidable = false) => All("V", X("Type"),
        Seq(OpenBracket, Call("Fintype", X("V")), CloseBracket, Comma, Sp,
            decidable
                ? Seq(OpenBracket, Call("DecidableEq", X("V")), CloseBracket, Comma, Sp,
                    All("G", Call("SimpleGraph", X("V")), body))
                : All("G", Call("SimpleGraph", X("V")), body)));
    private static Formula AlphaBody() => App(Q("Finset", "card"),
        App(Q("Finset", "filter"),
            Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(X("S"), Sp, Colon, Sp,
                Call("Finset", X("V")))), Sp, Mapsto, Sp,
                And(Eq(App(Q("Finset", "card"), X("S")), X("k")),
                    Call("IsGeneralPosition", X("G"), X("S"))))),
            Parenthesized(Seq(Q("Finset", "univ"), Sp, Colon, Sp,
                Call("Finset", Call("Finset", X("V")))))));
    private static Formula PsiBody() => Seq(F.Sum, Underscore,
        Grp(Seq(X("k"), Sp, InMacro, Sp, App(Q("Finset", "range"),
            new Formula.Binary(App(Q("Fintype", "card"), X("V")), FormulaBinaryOperator.Add, D(1))))), Sp,
        new Formula.Binary(App(Q("Polynomial", "C"),
                Parenthesized(Seq(Call("alpha", X("G"), X("k")), Sp, Colon, Sp, new Formula.Integers()))),
            FormulaBinaryOperator.Multiply, new Formula.Power(Q("Polynomial", "X"), X("k"))));
    private static Formula RealRootedBody() => All("z", X("Complex"),
        Imp(Eq(App(Q("Polynomial", "aeval"), X("z"), Call("psi", X("G"))), D(0)),
            Eq(App(Q("Complex", "im"), X("z")), D(0))));
    private static Formula ClaimBody() => GraphParameters(
        Imp(Call("Nonempty", X("V")), Imp(App(Q("SimpleGraph", "Connected"), X("G")),
            new Formula.Logic(Call("IsRealRooted", X("G")), FormulaLogicOperator.Iff,
                Eq(X("G"), Q("Top", "top"))))), true);
}
