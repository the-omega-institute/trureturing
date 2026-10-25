using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class UngradedLocalWordSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite local words admit a common vector power series on all signed exponents.",
        H("Ungraded Local Word Series"), Blocks(
            Paragraph(Text("Let V be a complex module and A a finite labelled family of actual VertexOperator maps. Labels are distinct even when their field values coincide. Choose a complete list with no repeated labels. Pairwise operator locality supplies a common order k independently of the input vector w. No energy, vacuum or weight is specified.")),
            Describe.Lean(DescribeId.Create("ungraded-local-word-common-series"),
                DeclarationHandle.Create(Prefix + "ungraded_local_word_common_series"),
                H("A common native vector series with exact signed recovery"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The clearing polynomial Q is the product of (z_i-z_j)^k over all i<j, acting by finite convolution on the original signed coefficient distributions. The imported common_cleared_fields supplies their order independence and coordinate lower bounds on w. Each field has a nonnegative truncation cutoff a_i on this same input. The common series P has coefficient at native multi-index d equal to the cleared distribution at d-a.")),
                    Paragraph(Text("For every permuted complete list and every signed exponent vector e, the cleared distribution at e-a equals P at the native multi-index e when all coordinates of e are nonnegative, and equals zero otherwise. The statement also gives the lower rectangle directly, uniformly in the remaining signed coordinates. The vector coefficients have no multiplication and P need not have finite support. Empty and singleton label types use the same construction.")),
                    Paragraph(Text("This is an algebraic common-series representation. It assumes neither positivity nor homogeneity, and proves no analytic convergence, collision substitution, associator or sewing law. The construction reuses the graded supplier's word, clearing polynomial and finite convolution without changing its finite homogeneous numerator theorem."))), DescribeRole.Theorem),
            Paragraph(Text("Finite Laurent convolution and signed zero extension commute with linear vector readouts. These laws are consumed by the canonical charge-sector application. The classical locality suppliers retain Matsuo-Nagatomo and Carnahan attribution; no literature novelty is claimed.")))));
}
