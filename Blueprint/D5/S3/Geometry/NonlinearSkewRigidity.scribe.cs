using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class NonlinearSkewRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Acute neighborhoods and exact skew difference identities for arbitrary maps of real inner product spaces.",
        H("Nonlinear skew rigidity"),
        Blocks(
            Paragraph(Text(
                "The carrier is any real inner product space, including the zero space and spaces "
                + "that are incomplete or infinite dimensional. The map is initially a total function. "
                + "No continuity, additivity or scalar compatibility is assumed. Its norm is a fixed "
                + "positive factor less than one times the input norm. For each pair of inputs, the "
                + "sum of their inner product and their output inner product, multiplied by the sum "
                + "of the two mixed inner products, is zero.")),
            Describe.Lean(
                DescribeId.Create("acute-difference"),
                DeclarationHandle.Create("D5/S3/Geometry/NonlinearSkewRigidity.exists_acute_skew_difference"),
                H("An acute ball forces exact skew differences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Around every nonzero vector v there is a positive radius epsilon such that "
                    + "the ball of radius three epsilon is strictly acute with margin r squared. "
                    + "Cauchy-Schwarz bounds the output inner product, so the first product factor "
                    + "is positive and the mixed factor vanishes throughout that ball. Subtracting "
                    + "the resulting skew identities at v+h and v gives the exact identity: the "
                    + "inner product of b with F(v+h)-F(v) equals minus the inner product of F(b) "
                    + "with h, for h of norm less than epsilon and b in the epsilon ball about v. "
                    + "Only the known inner product and norm enter the continuity argument."))),
                DescribeRole.Theorem))));
}
