using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovQuantum21Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Acyclicity at quantum degree 21", H("Acyclicity at quantum degree 21"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-quantum-21-integral-row"),
                DeclarationHandle.Create("D5/S3/Topology/FourBraidKhovanovQuantum21.quantum21_integral"),
                H("Acyclicity at quantum degree 21"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At normalized quantum degree 21, every cohomology group of the integral "
                    + "resolution cube vanishes. The checked integral contraction acts on the "
                    + "signed saddle maps of the displayed closed braid."))),
                DescribeRole.Theorem))));
}
