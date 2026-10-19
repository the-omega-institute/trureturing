using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;
internal sealed class DisconnectedReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/DisconnectedReflection.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native path reflection preserves actual weak support and active connectivity at the same vertices in both parities.",
        H("The Second Labelled Sector"), Blocks(
            Paragraph(Text("Reflection reverses and permutes the selected directed edges. It preserves their weak equivalence closure and their active endpoint set at each actual residue. The antipodal pair and the odd singleton obey their separate edge identities. The two sectors remain distinct native choices.")),
            Describe.Lean(DescribeId.Create("even-reflected-connectivity"), DeclarationHandle.Create(Prefix + "even_reflection_connected"),
                H("Even active connectivity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every admissible even parameter and every positive native path, the reflected decoded choice is ActiveConnected if and only if the original decoded choice is ActiveConnected. The support relation is transported on the same vertices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-reflected-connectivity"), DeclarationHandle.Create(Prefix + "odd_reflection_connected"),
                H("Odd active connectivity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The corresponding odd connectivity equivalence includes the singleton edge and preserves the original active-support predicate."))), DescribeRole.Theorem)), []));
}
