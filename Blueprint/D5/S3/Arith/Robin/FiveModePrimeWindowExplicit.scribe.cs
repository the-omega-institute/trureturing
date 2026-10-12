using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class FiveModePrimeWindowExplicitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/FiveModePrimeWindowExplicit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite 5040 six-cell has an exact normalized five-prime vector.",
        H("Exact Five Mode Vectors on the 5040 Six Cell"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("five-mode-prime-window-explicit"),
                DeclarationHandle.Create(Prefix + "goldenCell5040_prime_window_explicit"),
                H("Finite explicit window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each of the six values 5040, 10080, 15120, 20160, 30240 and "
                    + "60480, the theorem supplies u in {0,1,2} and v in {0,1} with "
                    + "n = 5040 * 2^u * 3^v.  Writing d = 13 + u + v, the coordinates "
                    + "in the order (2,3,5,7,83) are (5+u, 3+v, 2, 2, 1)/d, and "
                    + "the visible projection is (4+v, 3, 2)/d."))),
                DescribeRole.Theorem))));
}
