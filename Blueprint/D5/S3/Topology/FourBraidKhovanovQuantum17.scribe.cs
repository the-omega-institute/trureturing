using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovQuantum17Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral cohomology at quantum degree 17", H("Integral cohomology at quantum degree 17"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-quantum-17-integral-row"),
                DeclarationHandle.Create("D5/S3/Topology/FourBraidKhovanovQuantum17.quantum17_integral"),
                H("Integral cohomology at quantum degree 17"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quantum degree 17 has two integral generators in normalized degree 5 and "
                    + "one in degree 6. All other groups in the row vanish. The stage index counts "
                    + "one-smoothings, and conversion to normalized degree subtracts two."))),
                DescribeRole.Theorem))));
}
