using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class SymbolicCylinderShiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clopen symbolic cylinders and their exact shift pullback.",
        H("Clopen cylinders under the symbolic shift"),
        Blocks(
            Paragraph(Text(
                "For a finite discrete directed graph, History G is the compact legal "
                + "bi-infinite edge space. A cylinder fixes finitely many coordinates. "
                + "The formal results below make the symbolic-to-topological bridge explicit: "
                + "cylinders are clopen, and the left shift transports a cylinder by the "
                + "corresponding inverse translate of its center.")),
            Describe.Lean(
                DescribeId.Create("finite-cylinders-are-closed"),
                DeclarationHandle.Create(Prefix + "cylinder_closed"),
                H("Finite cylinders are closed"),
                StatementSource.FromAuthor(Disp(F.Id("cylinderClosed"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof identifies the cylinder with the inverse image of a finite "
                    + "product of singleton coordinate sets and uses the product topology "
                    + "and the subspace topology on legal histories."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-cylinders-are-clopen"),
                DeclarationHandle.Create(Prefix + "cylinder_isClopen"),
                H("Finite cylinders are clopen"),
                StatementSource.FromAuthor(Disp(F.Id("cylinderIsClopen"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Combining the existing finite-coordinate openness theorem with the "
                    + "closedness result gives the clopen basis used by symbolic dynamics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cylinders-form-a-local-basis"),
                DeclarationHandle.Create(Prefix + "exists_cylinder_subset"),
                H("Cylinders form a local topological basis"),
                StatementSource.FromAuthor(Disp(F.Id("existsCylinderSubset"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every open neighborhood of a legal history contains a finite-coordinate "
                    + "cylinder around that history. This is the local basis statement that "
                    + "turns finite symbolic observations into genuine topological neighborhoods."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shift-pulls-back-cylinders-exactly"),
                DeclarationHandle.Create(Prefix + "shift_preimage_cylinder"),
                H("The shift has an exact cylinder pullback"),
                StatementSource.FromAuthor(Disp(F.Id("shiftPreimageCylinder"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite coordinate set s and center x, the preimage under the "
                    + "left shift is the cylinder on s shifted by k↦k+1, centered at "
                    + "translate(-1,x). This equality is pointwise and does not use a "
                    + "metric, measure, entropy limit, or a hidden coding assumption."))),
                DescribeRole.Theorem))));
}
