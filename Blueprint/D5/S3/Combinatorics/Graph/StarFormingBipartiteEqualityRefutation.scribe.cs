using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class StarFormingBipartiteEqualityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bipartite equality for all positive k is false.", H("Bipartite equality for all positive k is false"),
        Blocks(
            Node("claim", "Conjecture 4.1", ClaimFormula(),
                "Rafik Sahbi, Upper k-Star-Forming Sets, k-Independence, and Upper Domination, "
                    + "arXiv:2610.03785v2, asserts equality for every bipartite finite graph and every positive integer k. "
                    + "The parameters beta and SF are the maximum k-independent cardinality "
                    + "and the maximum cardinality of an inclusion-minimal k-star-forming set. "
                    + "Graphs on Fin n represent finite simple graphs up to isomorphism.",
                DescribeRole.Definition),
            Node("result", "The conjectured equality is false", Disp(new Formula.Not(F.Id("claim"))),
                "Specializing the asserted equality to k equal to two gives equality for every bipartite graph at two. The ten-vertex bipartite graph has beta at most five and SF at least six, contradicting that specialization.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("sahbi-2026-star-forming-bipartite-all-k-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var g = F.Id("G");
        return Disp(Iff(F.Id("claim"), All("n", F.Id("Nat"), All("G", Call("SimpleGraph", Call("Fin", n)),
            All("k", F.Id("Nat"), Imp(Le(D(1), F.Id("k")),
                Imp(Call("Colorable", g, D(2)), Eq(Call("beta", g, F.Id("k")),
                    Call("SF", g, F.Id("k"))))))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static DocumentBlock Node(string selector, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("sfk-" + selector),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
