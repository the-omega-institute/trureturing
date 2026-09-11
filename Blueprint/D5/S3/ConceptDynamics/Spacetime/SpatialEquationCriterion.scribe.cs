using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class SpatialEquationCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Principal right multiples characterize spatial equations, with uniqueness in a domain.",
        H("The Abstract Spatial Equation Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spatial-equation-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion.spatial_equation_criterion"),
                H("Principal-multiple membership and unique nonzero solutions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a unital ring, the equation f * g = h is solvable exactly when h is a right "
                    + "multiple of f. In a ring without zero divisors, a nonzero f has at most one such "
                    + "solution; when f is zero, solvability is exactly h = 0 and every g solves the "
                    + "equation. The statement records these membership and cancellation guards "
                    + "without introducing a division algorithm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("principal-multiple-closure"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion.principalMultiples_sub"),
                H("The principal-multiple carrier is closed under subtraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Differences of principal multiples remain principal multiples by distributivity. "
                    + "This is a closure property of a general ring; computing a quotient is a "
                    + "separate question."))),
                DescribeRole.Theorem))));
}
