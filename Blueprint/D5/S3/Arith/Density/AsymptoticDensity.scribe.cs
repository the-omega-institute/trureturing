using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Density;

internal sealed class AsymptoticDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Density/AsymptoticDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Upper and lower asymptotic densities of sets of naturals, and subadditivity of the upper "
            + "density.",
        H("Asymptotic density of sets of naturals"),
        Blocks(
            Paragraph(Text(
                "The counting function of a set of naturals is the number of its members below a "
                    + "bound. Dividing by the bound and passing to the limit superior and the limit "
                    + "inferior gives the upper and the lower density; the set has a density when the "
                    + "two agree. Schnirelmann density, which Mathlib carries, is a different "
                    + "quantity: it is an infimum over all bounds rather than a limit, and it is not "
                    + "used here.")),
            Describe.Lean(
                DescribeId.Create("asymptotic-density-upper"),
                DeclarationHandle.Create(Prefix + "upperDensity"),
                H("Upper density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "upperDensity A is the limit superior along the natural numbers of the count of "
                        + "members of A below n, divided by n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("asymptotic-density-lower"),
                DeclarationHandle.Create(Prefix + "lowerDensity"),
                H("Lower density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "lowerDensity A is the limit inferior of the same ratio."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("asymptotic-density-has"),
                DeclarationHandle.Create(Prefix + "HasDensity"),
                H("Having a density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "HasDensity A d holds when the lower and upper densities of A agree and that "
                        + "common value is d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("asymptotic-density-union-subadditive"),
                DeclarationHandle.Create(Prefix + "upperDensity_union_le"),
                H("The upper density is subadditive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The upper density of a union is at most the sum of the upper densities. The "
                        + "proof runs through the finite counting functions, where the union bound is "
                        + "exact, and then through the limit superior of a sum, which is bounded by "
                        + "the sum of the limits superior once both are finite."))),
                DescribeRole.Theorem)),
        []));
}
