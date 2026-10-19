using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class AngleExtensionSliceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Geometry/Hyperideal/AngleExtensionSlice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first-slot cosine on the Section 68 scalar slice is not constant at its endpoint.",
        H("A scalar endpoint slice for the first-slot cosine"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("endpoint-slice"),
                DeclarationHandle.Create(Prefix + "endpointSlice"),
                H("First-slot cosine along the scalar slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The local edge order is (12,13,14,34,24,23). For a real parameter "
                        + "epsilon, endpointSlice(epsilon) is the original first-slot cosine "
                        + "at the six coordinates (2,2,2,17-epsilon,2,2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("endpoint-constant-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Constancy at the endpoint value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The claim says that every epsilon in the closed interval [0,1] "
                        + "has first-slot cosine equal to -1 along this slice."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("endpoint-slice-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The scalar slice leaves the endpoint value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At epsilon = 1/2, direct substitution into the two radicands and "
                        + "the numerator gives denominator 27 and cosine -17/18. This is "
                        + "different from -1, so the universal constancy claim is false. "
                        + "The result concerns this scalar cosine slice only; it does not "
                        + "assert an inverse-cosine regularity theorem or a global flow "
                        + "statement."))),
                DescribeRole.Theorem))));

}
