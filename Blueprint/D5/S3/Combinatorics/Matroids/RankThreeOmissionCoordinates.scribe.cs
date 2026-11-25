using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeOmissionCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeOmissionCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduced matrix coordinates for the integral rank-three lifting obstruction.",
        H("Reduced Omitted-Triangle Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-three-obstruction-matrix-kernel"),
                DeclarationHandle.Create(Module + ".rank_three_lifting_obstruction_equiv_kernel"),
                H("Reduced matrix for the integral obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose the bases on a finite ordered ground set of size n greater than three are all triples "
                    + "except a specified family whose distinct members meet in at most one point. "
                    + "For singleton parallel classes and any distinct root and anchor, the integral lifting obstruction "
                    + "is linearly equivalent over the integers to the kernel of the reduced omitted-triangle matrix modulo n. "
                    + "Each column is an increasing pair avoiding the root and anchor. "
                    + "The row of a triple evaluates the alternating form on two differences from the first point of the triple."))),
                DescribeRole.Theorem))));
}
