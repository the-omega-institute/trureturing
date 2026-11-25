using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class WeightedLogDerivativeResidueDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Boundary/WeightedLogDerivativeResidue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite weighted logarithmic derivatives have an exact residue and pole criterion.",
        H("Residues of weighted logarithmic derivatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-logarithmic-derivative-residue"),
                DeclarationHandle.Create(Owner + "weighted_log_deriv_residue"),
                H("Exact residue and removability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a finite family of meromorphic functions have finite signed orders at a common point, "
                    + "and assign each member a complex weight. The weighted sum of their logarithmic "
                    + "derivatives is, on a punctured neighborhood, the sum of an analytic function and "
                    + "the weighted sum of the orders divided by the displacement from the point. "
                    + "The germ has a simple pole exactly when that coefficient is nonzero. It admits "
                    + "an analytic extension exactly when the coefficient is zero. Each local factorization "
                    + "contributes the signed order of its power factor and the analytic logarithmic "
                    + "derivative of its nonvanishing factor. If every member is analytic at the "
                    + "center, all orders are nonnegative, and a vanishing member has positive order. "
                    + "With positive real weights, one positive summand and nonnegative remaining "
                    + "summands give a strictly positive real weighted sum. Its image in the complex "
                    + "numbers is the residue, so the germ has a simple pole."))),
                DescribeRole.Theorem))));
}
