using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters.FourCurrent;

internal sealed class MatchingRotationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic invariance of the labeled coefficient.",
        H("Cyclic invariance of the labeled coefficient"),
        Blocks(
            Describe.Lean(DescribeId.Create("four-current-coefficient-rotation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingRotation.bounded_coefficient_rotation"),
                H("Cyclic invariance of the labeled coefficient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original lattice D with positive-definite real Gram matrix, every current-label function i : Fin 4 → Fin D.rank and every natural grade quadruple n, boundedFourCurrentCoefficient D hD i n equals boundedFourCurrentCoefficient D hD (rotateFour i) (rotateFour n). The rotation permutes all ten labeled matchings, their edge assignments, arc sides and independent winding coordinates bijectively."))), DescribeRole.Theorem),
            Paragraph(Text("The module retains the original constant-grade matching proof, cyclic edge and side equivalences, signed Gram symmetry and exact bounded finite residual, division and geometric sums. Rotation preserves the minimum and maximum grade and the complete charge cutoff. These results are consumed by the root energy-channel reduction and final all-grade endpoint. The finite identity makes no thermal convergence, annular, modular, sewing or physical-realization claim.")))));
}
