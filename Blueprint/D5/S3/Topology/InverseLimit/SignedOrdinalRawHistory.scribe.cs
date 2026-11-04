using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalRawHistoryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalRawHistory.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SignedOrdinalRawHistory", H("Concrete RawHistory on the actual diagram"), Blocks(
            Describe.Lean(DescribeId.Create("signedordinalrawhistory-raw-history"),
                DeclarationHandle.Create(Owner + "rawHistory"), H("Concrete RawHistory on the actual diagram"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The concrete RawHistory on finalPrefix.diagram is populated with the actual U and its surjectivity, original V, whole nu and its surjectivity, actual cofinal launches, permanent disjoint reservoirs, original eligible J, infinite intersections and directed finite differences. Its proper F directly applies the canonical history proper_f through equality of the literal carrier and the original whole measure readback. The actual incoming regular bounded evidence is preserved. The full canonical run remains available with its selected ordinary or delayed Result and quantitative G; RawHistory alone does not encode G."))), DescribeRole.Definition),
            Paragraph(Text("No final endpoint is asserted.")))));
}
