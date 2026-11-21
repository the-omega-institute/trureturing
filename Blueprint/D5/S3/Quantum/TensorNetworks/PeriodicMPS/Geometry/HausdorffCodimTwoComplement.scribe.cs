using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Geometry;

internal sealed class HausdorffCodimTwoComplementDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Geometry/HausdorffCodimTwoComplement";
    private const string Title = "Path-connected complements of sets of small Hausdorff dimension";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("hausdorffcodimtwocomplement-path-connected-complement"),
            DeclarationHandle.Create(Module + ".isPathConnected_diff_of_dimH_add_one_lt"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let U be open and connected in a finite-dimensional real normed space of dimension d. If the Hausdorff dimension of B plus one is strictly less than d, then U minus B is path connected and dense in U.")),
                Paragraph(Text("Inside a convex neighborhood, project the excluded set from each endpoint onto a common transverse slice. Each projected set has Hausdorff dimension below that of the slice. Choosing a point outside both projected sets yields two line segments in the complement. Relative density and the connectedness of U extend this local construction to paths across U.")),
                Paragraph(Text("For a closed B of Hausdorff dimension at most d minus two with d at least two, the complement is also open."))),
            DescribeRole.Theorem))));
}
