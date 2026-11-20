using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class CantorCircleExpansivityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/CantorCircleExpansivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact positive expansivity on circles glued along the Cantor set",
        H("Exact positive expansivity on circles glued along the Cantor set"),
        Blocks(
            Paragraph(Text("Tripling on the additive circle preserves the image of the ternary Cantor set. The induced map on finitely many copies glued along that image is continuous and surjective.")),
            Describe.Lean(
                DescribeId.Create("cantor-circle-near-coalescing-point"),
                DeclarationHandle.Create(Owner + "exists_near_coalescing_point"),
                H("Points enter the Cantor image after one iterate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take positive Cantor points x approaching zero. The points (1 + x)/3 lie in the open middle third, approach the Cantor endpoint 1/3, and triple to x modulo one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cantor-circle-exact-expansion-order"),
                DeclarationHandle.Create(Owner + "exact_order"),
                H("The least expansion order is the number of circles"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a small scale a strict forward Bowen ball projects to one point of the circle. Its fiber contains at most N points. At every positive scale there is a fiber of N distinct points with arbitrarily small diameter whose points all agree after one iterate.")),
                    Paragraph(Text("The carrier is compact and connected because it is a finite union of compact connected circles sharing the image of the Cantor set."))),
                DescribeRole.Theorem))));
}
