using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class JacoExponentialDominationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/JacoExponentialDominationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kok2025jaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The A000149 vertices fail the domination clause of Kok's Conjecture 2.12.",
        H("The Domination Clause of Kok's Jaco Graph Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("jaco-right-endpoint"),
                DeclarationHandle.Create(Prefix + "jacoRight"),
                H("Right endpoints in the infinite linear Jaco graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For vertex n, the right endpoint is 2n minus the number of earlier "
                        + "positive vertices whose right endpoints reach n. The recursive "
                        + "table evaluates these endpoints from left to right."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jaco-right-successor-growth"),
                DeclarationHandle.Create(Prefix + "jacoRight_succ_ge"),
                H("Strict growth of right endpoints"),
                StatementSource.FromAuthor(SuccessorGrowthFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Every earlier endpoint counted at level n+1 is also counted at level n. "
                        + "Only vertex n itself can be the additional index, so the indegree "
                        + "count rises by at most one while the doubled vertex index rises by "
                        + "two. Therefore the right endpoint rises by at least one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jaco-undirected-adjacency"),
                DeclarationHandle.Create(Prefix + "Adj"),
                H("Undirected Jaco adjacency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For two distinct indices, the lower vertex is adjacent to the higher "
                        + "exactly when its right endpoint reaches the higher index."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jaco-exponential-vertices"),
                DeclarationHandle.Create(Prefix + "exponentialVertices"),
                H("The A000149 vertex indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The selected indices are the natural floors of e to a natural-number "
                        + "power. Exponent zero supplies the artificial first term 1 used in "
                        + "the source statement."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jaco-domination"),
                DeclarationHandle.Create(Prefix + "Dominates"),
                H("Domination of positive vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A set dominates when each positive vertex either belongs to the set or "
                        + "is adjacent to one of its members."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jaco-domination-clause"),
                DeclarationHandle.Create(Prefix + "dominationClause"),
                H("The domination clause"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The first clause of Conjecture 2.12 says that A000149 indexes a gamma-set "
                        + "of the infinite linear Jaco graph. Every gamma-set is dominating, so "
                        + "this definition records that necessary domination assertion. The "
                        + "minimum-cardinality and p-graphical assertions are not included."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jaco-domination-clause-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Vertex 88 is not dominated"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The right endpoint at vertex 54 is 87 and the right endpoint at "
                            + "vertex 88 is 143. Strict endpoint growth shows that every "
                            + "selected index at most 54 has endpoint below 88.")),
                    Paragraph(Text(
                        "Certified bounds for e put every A000149 term either at most 54 or "
                            + "at least 144. Thus vertex 88 is neither selected nor adjacent "
                            + "to a selected vertex. The domination clause is false, which "
                            + "refutes the gamma-set assertion. No conclusion is drawn about "
                            + "the separate p-graphical clause."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kok-jaco-exponential-domination-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula SuccessorGrowthFormula()
    {
        var n = F.Id("n");
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            new Formula.Relation(
                new Formula.Binary(Call("jacoRight", n), FormulaBinaryOperator.Add, D(1)),
                FormulaRelationOperator.LessThanOrEqual,
                Call("jacoRight", new Formula.Binary(n, FormulaBinaryOperator.Add, D(1))))));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("dominationClause")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
