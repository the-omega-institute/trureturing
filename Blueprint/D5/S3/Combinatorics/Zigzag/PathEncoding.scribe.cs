using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class PathEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/PathEncoding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete indexed path becomes the original ordered form list, with an exact flow identity connecting accumulated charge to the choice's imbalance.",
        H("Encoding Paths as Zigzag Choices"),
        Blocks(
            Describe.Lean(DescribeId.Create("form-list-flow"),
                DeclarationHandle.Create(Prefix + "formsFlow"), H("Flow of an ordered form list"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At starting class k, formsFlow sums the directed edge-flow contributions of successive labels. It keeps list order and each label; it is the bridge from the recursive path type to the exact class-by-class integer imbalance."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-path-flow-boundary"),
                DeclarationHandle.Create(Prefix + "evenPathFlow_eq_boundary"),
                H("Even path flow reaches the antipodal boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "After 3r-3 interior steps and the antipodal form pair, the full n=6r path flow is boundaryFlow of its recorded charge. The proof inducts over labelled tails, applies Retirement's transition identity, then uses the even terminal flow theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-path-flow-boundary"),
                DeclarationHandle.Create(Prefix + "oddPathFlow_eq_boundary"),
                H("Odd path flow reaches the singleton boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The n=6r+3 path has 3r-1 interior steps and one central terminal form. Its full flow is the boundaryFlow of its charge. The distinct odd terminal identity is necessary here; no closure of an edge cycle is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-path-choice"),
                DeclarationHandle.Create(Prefix + "evenPathChoices"),
                H("Encode an even path as an actual choice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The start, each low/high transition pair, and the antipodal terminal are flattened into exactly one form for each source class. The first-class restriction follows from its start index. The oddPathChoices definition performs the corresponding singleton construction."))),
                DescribeRole.Definition)), []));
}
