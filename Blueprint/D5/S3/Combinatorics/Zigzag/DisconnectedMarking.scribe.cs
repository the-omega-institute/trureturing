using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;
internal sealed class DisconnectedMarkingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/DisconnectedMarking.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual root-separating coloring determines a complete absolute successor word on every positive native path.",
        H("Recovering Words from Actual Separation"), Blocks(
            Paragraph(Text("The marking table records colors of the actual signed endpoint roles. Live separated states force three-step blocks, while the dead states have neither a separated continuation nor a separated cap. The inverse uses actual endpoint colors; it does not assume six distinct roles at the antipode.")),
            Describe.Lean(DescribeId.Create("even-native-separation-inverse"), DeclarationHandle.Create(Prefix + "even_native_separation_code"),
                H("The even native inverse"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r at least one and every positive native even path, a coloring that separates the roots and is equal on every actual selected edge yields an initial bit and successor word whose coded path is exactly the given path. The assertion recovers labels and all steps, including the even cap, without a separate charge assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-native-separation-inverse"), DeclarationHandle.Create(Prefix + "odd_native_separation_code"),
                H("The odd native inverse"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The odd counterpart forces the two final moves and singleton cap and recovers every original path label at the odd tail length."))), DescribeRole.Theorem)), []));
}
