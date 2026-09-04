using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenThirdOrderFreeLieBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenThirdOrderFreeLieBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero degree-three free-Lie primitive strictly refines an explicit prime-golden step-two chronology fiber.",
        H("Prime-Golden Third-Order Free-Lie Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-third-order-free-lie-strictness"),
                DeclarationHandle.Create(
                    Prefix + "explicit_degree_three_strict_refinement"),
                H("A concrete degree-three observer escapes a full step-two fiber"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ABBA and BAAB histories have the same prime-golden bidegree, the same scalar Euler trajectory at every time, and the same complete step-two chronological signature under the explicit integer-matrix observation.")),
                    Paragraph(Text(
                        "Their cubic difference is the represented free-Lie primitive minus the bracket of the sum with the first commutator. The E12 and E21 representation evaluates it to a concrete nonzero integer matrix.")),
                    Paragraph(Text(
                        "This proves strict refinement for one genuine residual fiber. It does not assert that degree three separates every finite chronology."))),
                DescribeRole.Theorem))));
}
