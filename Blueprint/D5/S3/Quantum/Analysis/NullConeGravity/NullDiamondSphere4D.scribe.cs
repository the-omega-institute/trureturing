using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondSphere4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Round celestial measure and square integrability of the angular logarithm.",
        H("Round measure on the celestial two-sphere"),
        Blocks(
            Entry("round-measure", "sphereMeasure", "Round measure",
                "Equip the unit sphere in three-dimensional Euclidean space with the sphere measure "
                + "induced by Euclidean volume.", DescribeRole.Definition),
            Entry("dot-pushforward", "sphere_dot_pushforward", "Distribution of the dot product",
                "For every fixed unit vector n, the dot product with n sends round measure to 2π "
                + "times Lebesgue measure on the closed interval from −1 to 1. "
                + "Slice the solid cone of directions above a nonnegative threshold into planar disks. "
                + "Their areas give the upper-tail measure, and reflection handles negative thresholds."),
            Entry("round-mass", "sphere_measure_univ", "Total mass",
                "The round sphere has measure 4π."),
            Entry("angular-diagonal", "sphere_diag_null", "Angular diagonal",
                "The pairs with dot product one form a null set for the product of round measures. "
                + "For each fixed first coordinate the dot-product distribution assigns zero mass to one."),
            Entry("log-square-interval", "intervalIntegrable_log_sq", "Logarithm squared near zero",
                "The square of the real logarithm is interval integrable from zero to two."),
            Entry("angular-log-square", "sphere_log_sq_integrable", "Square-integrable angular logarithm",
                "Apply the dot-product distribution and the substitution t = 1 − x in each angular section. "
                + "The squared logarithm of one minus the dot product is integrable on the product sphere. "
                + "This supplies the angular integrability used in the square-root trace criterion of Satishchandran and Sorce."),
            Entry("angular-log-integral", "sphere_log_sq_integral", "Angular integral",
                "The integral of the squared angular logarithm over the product sphere equals "
                + "8π² times the integral of the squared logarithm from zero to two."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
