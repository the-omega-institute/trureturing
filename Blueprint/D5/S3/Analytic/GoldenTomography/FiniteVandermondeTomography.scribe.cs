using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FiniteVandermondeTomographyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Distinct finite phase nodes make the Vandermonde moment observer faithful.",
            H("Finite Vandermonde Tomography"),
            Blocks(
                Theorem(
                    "distinct-nodes-give-a-nonzero-vandermonde-determinant",
                    "vandermonde_det_ne_zero_of_injective",
                    "Distinct Nodes Give a Nonzero Determinant",
                    "An injective node family makes every Vandermonde difference factor nonzero, hence the determinant is nonzero."),
                Theorem(
                    "distinct-nodes-give-a-nondegenerate-vandermonde-form",
                    "vandermonde_nondegenerate_of_injective",
                    "Distinct Nodes Give a Nondegenerate Form",
                    "The nonzero determinant yields a nondegenerate Vandermonde bilinear form."),
                Theorem(
                    "finite-vandermonde-moments-are-faithful",
                    "finite_moment_readout_injective",
                    "Finite Vandermonde Moments Are Faithful",
                    "The first n moments recover an n-component amplitude vector whenever the n phase nodes are pairwise distinct."),
                Theorem(
                    "finite-moment-equality-is-amplitude-equality",
                    "finite_moments_eq_iff",
                    "Finite Moment Equality Is Amplitude Equality",
                    "Under node separation, two amplitude vectors have the same finite moment packet exactly when they are equal."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(paragraph)),
                Paragraph(Text(
                    "The result is exact finite tomography. It supplies no uniform lower bound "
                        + "for a singular value or inverse condition number."))),
            DescribeRole.Theorem);
}
