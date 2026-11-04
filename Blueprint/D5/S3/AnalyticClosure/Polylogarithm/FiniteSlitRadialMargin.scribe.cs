using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class FiniteSlitRadialMarginDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitRadialMargin.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive radial margin for admissible compositions",
        H("FiniteSlitRadialMargin"), Blocks(
            Describe.Lean(DescribeId.Create("signed-prefix-margin"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A positive radial margin for admissible compositions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text("For every positive head greater than one, every positive-entry tail and positive reciprocal power, the actual normalized reciprocal has a uniform strictly positive radial quotient (A(r)-endpoint)/(1-r) near one. CompositionBoundary supplies the positive total Z of the original source coefficients, and CompositionDisk supplies strict positivity of the coefficient f(1).")),
                    Paragraph(Text("For 0<r<1 the positive source series has value x with 0<x<=Z. Its exact difference from Z is at least f(1)(1-r). Comparing inverse powers gives the lower bound f(1)/Z^2 times Z^(-k), where ell=k+1. Source agreement with the normalized continuation identifies this real estimate with the actual reciprocal, preserving the removable origin and ordinary normalization.")),
                    Paragraph(Text("This result covers the admissible branch only. No logarithmic growth estimate or radial margin for a leading head equal to one is claimed here; the complete original event retains that obligation."))), DescribeRole.Theorem))));
}
