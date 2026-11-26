using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class UniformMatroidCircuitCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/UniformMatroidCircuitCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two equations for the uniform core.",
        H("Uniform Matroid Circuit Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("form-mem-weighted-iff"),
                DeclarationHandle.Create(Module + ".form_mem_weighted_iff"),
                H("The two equations for the uniform core"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a matroid on the full finite ground whose bases are all subsets of the stated "
                    + "positive size, let a take the value one on each vector of the chosen basis. The form "
                    + "coordinates, extended by zero off the matroid bases, belong to the weighted residue "
                    + "group exactly when covector multiplication by a and insertion of the basis vector sum "
                    + "weighted by class sizes both vanish."))),
                DescribeRole.Theorem))));
}
