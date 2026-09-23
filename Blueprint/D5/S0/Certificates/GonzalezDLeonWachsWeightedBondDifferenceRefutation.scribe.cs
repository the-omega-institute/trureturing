using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class GonzalezDLeonWachsWeightedBondDifferenceRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three disjoint triangles and three spanning paths refute Conjecture 4.13(2).",
        H("Weighted Bond Difference Counterexample"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-bond-difference-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The literal all-graphs conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every finite graph G and spanning subgraph H with the same number "
                        + "of connected components, the sign-corrected difference of their literal "
                        + "source Mobius polynomials is asserted to split over the reals. This is "
                        + "part (2) as written; no connected-only premise is added."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-bond-difference-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The nine-vertex witness refutes part (2)"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "On Fin 3 x Fin 3, G is three triangle fibers and H is three path fibers. "
                        + "Both have three components and H is proper. Restriction and gluing give "
                        + "the source-poset product, hence polynomials A^3 and B^3. Their difference "
                        + "is (X+1)^2 times a quartic with no real root, so it does not split."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "gonzalez-dleon-wachs-conjecture-4-13-2-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimFormula() => Disp(Equal(
        F.Id("claim"), Call("ConjecturePartTwo")));

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
