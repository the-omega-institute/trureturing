using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryBirthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistoryBirth.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole canonical birth packs", H("Whole canonical birth packs"), Blocks(
            Describe.Lean(DescribeId.Create("signedordinalhistorybirth-0"),
                DeclarationHandle.Create(Owner + "prepared_old_readback"), H("All old whole labels are retained"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A BirthPack contains the support enumeration U, natural clopen enumeration B, chosen support family V and complete BornData enumeration nu on every Label. Preparation preserves every older whole pack through oldV and oldNu, including labels that are not yet eligible for J. B is read from the original birth. Literal carrier equality changes neither labels nor enumeration indices; permanent N arrivals are a separate object."))), DescribeRole.Theorem))));
}
