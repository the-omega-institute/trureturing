using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class OddPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/OddPaths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd central singleton has its own complete inverse, so the literal balance-only count is obtained in both parities.",
        H("Odd Balanced-Choice Correspondence"),
        Blocks(
            Describe.Lean(DescribeId.Create("odd-charge-reflection"),
                DeclarationHandle.Create(Prefix + "oddPathReflection_charge"),
                H("Reflection negates the odd path charge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The opposite sector has different form labels at the central singleton as well as at the interior steps. The explicit reflection is an equivalence and sends the accumulated charge to its negative; therefore both signed zero-charge sectors have equal cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-choice-equivalence"),
                DeclarationHandle.Create(Prefix + "oddBalancedChoicesEquiv"),
                H("Balanced odd choices are exactly zero-charge paths"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every r>=1, balanced Choices (2r+1), where n=6r+3, are equivalent to the two signed OddPath sectors with 3r-1 interior steps and zero charge. Surjectivity classifies each low/high label pair of an arbitrary balanced choice, then separately classifies the singleton terminal. The final nonzero semitone balance equation forces charge zero; DecodedBalance gives injectivity. The odd case is not inferred from the even antipodal proof."))),
                DescribeRole.Definition)), []));
}
