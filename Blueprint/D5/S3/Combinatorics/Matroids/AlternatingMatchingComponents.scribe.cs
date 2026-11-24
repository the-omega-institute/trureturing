using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class AlternatingMatchingComponentsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The component of two perfect matchings is a square exactly at their commuting vertices.",
        H("Components of Two Perfect Matchings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("matchings"),
                DeclarationHandle.Create(Module + ".Matchings"),
                H("Distinct matching partners"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two functions on the vertex type are involutions without fixed points and give distinct partners at each vertex."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("matching-union"),
                DeclarationHandle.Create(Module + ".graph"),
                H("Union graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An edge joins a vertex to either of its two partners."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("commuting-square"),
                DeclarationHandle.Create(Module + ".component_eq_square"),
                H("The component at a commuting vertex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Where applying the two involutions in either order gives the same vertex, the component consists of the start, the two partners, and that common endpoint. These vertices are closed under both matchings and each is reachable from the start."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommuting-six"),
                DeclarationHandle.Create(Module + ".six_le_component_of_noncommute"),
                H("Six vertices in a noncommuting component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a finite vertex type, disagreement between the two compositions gives at least six vertices in the component. The start, the two one-step endpoints, the two ordered two-step endpoints, and the endpoint of a first-second-first path are all distinct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommuting-component"),
                DeclarationHandle.Create(Module + ".noncommute_iff_six_le_component"),
                H("Component size detects noncommutation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a finite vertex type, the compositions disagree at the start if and only if its component has at least six vertices. In the commuting case the four enumerated vertices are distinct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("divisibility-large-component"),
                DeclarationHandle.Create(Module + ".exists_large_component_of_not_dvd"),
                H("A component of size at least six"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the number of vertices in a finite graph formed by the two matchings is not divisible by four, some component has at least six vertices. Otherwise the component sizes would all be four and would sum to a multiple of four."))),
                DescribeRole.Theorem))));
}
