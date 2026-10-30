using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class ReflectionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual charged residue comparison.",
        H("Reflections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-double-reflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/Reflections.transformedCollisionKernel_double_reflection"),
                H("Double coordinate reflection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For an arbitrary oscillator polynomial and actual ground vector, reflecting both charges multiplies the actual transformed collision kernel by (-1)^(gamma+delta). Odd oscillator frequencies preserve translated support and attach its exact coefficient character. Even lattice norms cancel that character with the creation character. The actual ground actions are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-four-reflection-diagonal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/Reflections.charged_reflected_collision_diagonal"),
                H("All four reflected kernels on one actual diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("Both matching lift equations reduce the four projected kernels to half the sum of the unreflected kernel and its signed right reflection. The latter contributes (-1)^v on the common creation diagonal. This gives precisely the two-pole weights, with each negative collision degree tested separately and with the original chargeScalar and ordered ground-action factors."))),
                DescribeRole.Theorem))));
}
