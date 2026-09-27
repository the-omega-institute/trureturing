using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class Erdos203SixCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This is a proved prerequisite for the 252-row obstruction. It does not certify the seventh-row capacity factor, the 96 numerical deficits, a positive 252-row missed fraction, or the whole Erdos 203 problem.",
        H("Conditional capacity after six original rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-sixrect"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.SixRect"),
                H("Six-row rectangular transversal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("SixRect is Fin 360 times Fin 24, of cardinality 8640."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-sixrepresentative"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.sixRepresentative"),
                H("Representative on the full period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The representative sends the integer coordinates of q through periodMap."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-sixassembly"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.sixAssembly"),
                H("Assembling a coset point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map adds the representative of q to an element of sixTorus."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-sixregion"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.sixRegion"),
                H("Union of selected whole cosets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A torus point z belongs precisely when z minus some sixRepresentative q belongs to sixTorus for a q in U."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-restrictedgcd"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.restrictedGcd"),
                H("Restricted image gcd"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For row i this is gcd(e_i,gcd(360 a_i,228 a_i + 24 b_i))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-originalresidue"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.originalResidue"),
                H("Original residual phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q in SixRect, this is a_i q.1 + b_i q.2 reduced modulo restrictedGcd i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-sixmissed"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.sixMissed"),
                H("Representatives missed by six rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This Finset selects the representatives at which all six original forms differ from the corresponding fixed original phases."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-0"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.histogramMaximum"),
                H("Original-residue histogram maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The maximum is computed from the actual original linear form modulo its restricted image gcd on the selected rectangle subset. It is not an assumed capacity oracle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203sixcapacity-1"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SixCapacity.six_row_conditional_capacity"),
                H("Actual six-row conditional capacity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rectangle times the six-row kernel maps bijectively to the full torus. The selected missed cosets equal the actual six-row uncovered region. For every subset U, original row and original phase, e times 8640 times the intersection cardinality is at most M squared times g times the largest original-residue histogram bucket in U."))),
                DescribeRole.Theorem)),
        []));
}
