using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockRetainedEnergyGaussianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyGaussian.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full retained energy Gaussian", H("Retained Creation Energy"), Blocks(
            Paragraph(Text("The original lattice datum D has no positivity or occupation hypothesis. "
                + "The charges a and b and every oscillator energy are unrestricted. "
                + "F_e is the original correctedSource(a+b,creationCoeff(a,e)). "
                + "Its retained polynomial contains every normal variable X(some i) and the shift X(none). "
                + "The previously proved scalar G_e is an algebra evaluation, not a vacuum matrix element. "
                + "Its scalar proof is reused without replacing the full retained polynomial.")),
            Describe.Lean(DescribeId.Create("actual-full-retained-energy-recurrence"),
                DeclarationHandle.Create(Prefix + "actual_full_retained_energy_recurrence"),
                H("Full Retained Energy Convolution"),
                StatementSource.FromAuthor(Disp(Call("FullRetainedEnergyRecurrence", F.Id("D"),
                    F.Id("a"), F.Id("b"), F.Id("e")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The exact original contraction and insertion equations yield (e+1) F_(e+1) as a finite "
                    + "convolution against the normal multiplier sum_l a_l X(some(l,k)) and "
                    + "C((k+1) h_(k+1)) X(none)^(k+1). The coefficient h is the original chargedEnergyLogCoefficient. "
                    + "The coordinate pairing is contracted before the finite triangular energy region is regrouped "
                    + "by total pair energy. The existing ordered-pair reflection supplies the half exactly once. "
                    + "No retained variable is evaluated away. Every summation is over its genuine finite energy support. "
                    + "This source-side polynomial identity does not establish a product-side recurrence or either all-j branch identity."))),
                DescribeRole.Theorem))));
}
