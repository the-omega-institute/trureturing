using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class FiniteTraceDeterminantMassDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual trace fibers and exact uniform mass for a fixed nonzero determinant.",
        H("Trace laws over finite fields"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-finite-matrix-trace-det-fiber"),
                DeclarationHandle.Create(Module + "matrix_trace_det_fiber_card"),
                H("Trace and determinant fibers reduce to a quadratic root count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first diagonal coordinate fixes the other. The two off-diagonal coordinates "
                    + "must have a specified product, giving an explicit cardinality decomposition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-finite-trace-fiber-quadratic-character"),
                DeclarationHandle.Create(Module + "matrix_trace_det_quadratic_character_card"),
                H("The quadratic character gives the exact trace fiber size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Completing the square identifies the remaining quadratic roots with the square roots "
                    + "of the characteristic discriminant in the actual odd finite field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-finite-nonzero-determinant-fiber"),
                DeclarationHandle.Create(Module + "det_fiber_card"),
                H("Every nonzero determinant fiber has the special linear group size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Scaling the first row by the inverse determinant gives a bijection to the special "
                    + "linear group, with no choice of a matrix representative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-finite-uniform-trace-mass"),
                DeclarationHandle.Create(Module + "uniform_trace_mass"),
                H("Uniform conditional trace mass is an exact rational ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The trace-fiber cardinality divided by the determinant-fiber cardinality is the "
                    + "exact finite conditionally uniform law. It provides a counting input for "
                    + "arithmetic readouts, not a theorem of Frobenius equidistribution."))),
                DescribeRole.Theorem))));
}
