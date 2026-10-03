using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MostowPrasadCoveringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/MostowPrasadCovering.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Isometric representations connect to standard orbit quotients and covering maps.",
        H("Isometric orbit coverings"),
        Blocks(
            Paragraph(Text(
                "The representation action identifies the project's orbit quotient with "
                    + "Mathlib's standard orbit quotient. Under explicit freeness and proper "
                    + "discontinuity assumptions, its projection is a topological covering map. "
                    + "No finite-volume lattice or hyperbolic geometry is constructed here.")),
            Describe.Lean(
                DescribeId.Create("mostow-covering-representation-action"),
                DeclarationHandle.Create(Prefix + "representationMulAction"),
                H("Action associated with an isometric representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The group acts by applying its represented isometries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-covering-standard-quotient"),
                DeclarationHandle.Create(Prefix + "StandardOrbitQuotient"),
                H("Standard orbit quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mathlib's orbit quotient for the representation action."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-covering-free-representation"),
                DeclarationHandle.Create(Prefix + "FreeRepresentation"),
                H("Free representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only the identity group element fixes a point."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-covering-proper-representation"),
                DeclarationHandle.Create(Prefix + "ProperlyDiscontinuousRepresentation"),
                H("Properly discontinuous representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Only finitely many group elements move one compact set to meet another."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-covering-standard-homeomorphism"),
                DeclarationHandle.Create(Prefix + "standardOrbitHomeomorph"),
                H("Homeomorphism with the standard orbit quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two orbit conventions give canonically homeomorphic quotient spaces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-covering-projection"),
                DeclarationHandle.Create(Prefix + "orbitQuotientMk_isCoveringMap"),
                H("Covering projection for a free proper action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quotient projection is a covering map when the representation is free "
                        + "and properly discontinuous on a locally compact Hausdorff space."))),
                DescribeRole.Theorem)),
        []));
}
