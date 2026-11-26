using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMActualMetricCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invertible Euclidean coordinates for the finite BKM form and order of the relative operator.",
        H("Euclidean coordinates for the finite BKM metric"),
        Blocks(
            Entry("omega-coefficient-pos-def", "omegaCoefficient_posDef", "Positive definite BKM coefficient",
                "The coefficient of a positive definite input is positive definite. Compare the input to a positive multiple of the identity and use the coefficient of the identity.", DescribeRole.Theorem),
            Entry("relative-operator", "relativeOperator", "Relative operator",
                "In Euclidean coordinates the coefficient of a is conjugated by the inverse square root of the coefficient of b.", DescribeRole.Definition),
            Entry("relative-operator-self-adjoint", "relativeOperator_selfAdjoint", "Self-adjoint relative operator",
                "Positivity of the coefficient of a is preserved by conjugation with the self-adjoint inverse square root.", DescribeRole.Theorem),
            Entry("relative-operator-bounds", "relativeOperator_bounds", "Relative operator sandwich",
                "Under ℓb ≤ a ≤ ub for positive definite a and b and 0 < ℓ ≤ u, the relative operator lies between ℓI and uI. Conjugation turns the reference coefficient into the identity.", DescribeRole.Theorem),
            Entry("metric-coordinates", "metricCoordinates", "Invertible BKM coordinates",
                "Vectorize a matrix and apply the positive square root of the BKM coefficient. Its inverse uses the inverse square root and inverse vectorization.", DescribeRole.Definition),
            Entry("bkm-inner", "bkmInner", "Observable BKM form",
                "The observable form on X and Y is the trace of X* times the BKM power integral applied to Y.", DescribeRole.Definition),
            Entry("metric-coordinates-inner", "metricCoordinates_inner", "Realization of the BKM inner product",
                "The Euclidean inner product of the coordinates equals the observable BKM form at the reference input.", DescribeRole.Theorem),
            Entry("relative-operator-inner", "relativeOperator_inner", "Realization of the second BKM form",
                "In the coordinates for b, insertion of the relative operator gives the observable BKM form at a.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
