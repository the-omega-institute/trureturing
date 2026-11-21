using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.CoveringDimension;

internal sealed class GluedCircleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/CoveringDimension/GluedCircle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-dimensional continua of every finite positive expansivity order",
        H("One-dimensional continua of every finite positive expansivity order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("glued-circle-covering-dimension-upper-bound"),
                DeclarationHandle.Create(Owner + "atMost_one_gluedCircle"),
                H("Finite graph sheets over a circle have covering dimension at most one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A metric sphere on the circle has at most two points. Balls therefore give a basis of open sets with finite frontiers. The projection of finitely many compact graph sheets onto the base is closed with finite fibers, so the covering-dimension bound pulls back."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cantor-circle-one-dimensional-exact-expansion-order"),
                DeclarationHandle.Create(Owner + "cantorCircle_exactOrder_oneDimensional"),
                H("Every order N at least two occurs on a one-dimensional continuum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Glue N circles along the ternary Cantor image and apply tripling on each circle. The carrier is a nontrivial connected compact metric space. Its covering dimension is exactly one by the closed finite-to-one projection and the connectedness lower bound.")),
                    Paragraph(Text("The induced continuous surjection has a positive scale at which every strict forward Bowen ball contains at most N points. At each positive scale some ball contains at least N points. This is an existence result within Gangloff, Guillon and Oprocha's Question 3.2, which asks for a classification of one-dimensional continua."))),
                DescribeRole.Theorem))));
}
