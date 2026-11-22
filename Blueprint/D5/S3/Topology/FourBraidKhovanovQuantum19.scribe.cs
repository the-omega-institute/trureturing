using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovQuantum19Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Acyclicity at quantum degree 19", H("Acyclicity at quantum degree 19"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-quantum-19-integral-row"),
                DeclarationHandle.Create("D5/S3/Topology/FourBraidKhovanovQuantum19.quantum19_integral"),
                H("Acyclicity at quantum degree 19"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed integral complex at normalized quantum degree 19 is acyclic. "
                    + "The certificate includes each homological degree of the row and proves "
                    + "that every cycle is a boundary."))),
                DescribeRole.Theorem))));
}
