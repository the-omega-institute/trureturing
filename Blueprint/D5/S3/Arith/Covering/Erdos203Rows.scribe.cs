using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class Erdos203RowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal input for the fixed 252-row core after removing moduli divisible by 23. Coefficients, moduli and integer phase domains are unchanged.",
        H("The original 252 modular rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-row"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.Row"),
                H("Original congruence row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A row stores the prime label p, original modulus e, and original coefficients a,b as natural numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-period"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.period"),
                H("Common original period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The period is the literal natural number 17599117536000. It is the least common multiple of the 252 retained original moduli."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-baserows"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.baseRows"),
                H("Seven base rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seven original rows have prime labels 5,7,11,13,17,19,23 and moduli 4,6,10,12,16,18,11, with their original coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-tailrows"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.tailRows"),
                H("Remaining original rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The 245 literal tail rows follow the seven base rows in the original input order. Precisely the input rows with modulus divisible by 23 are omitted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-phases"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.Phases"),
                H("One global phase vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Phases is Fin 252 to integers. Its value at a row is fixed before either exponent coordinate is chosen."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-shiftphases"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.shiftPhases"),
                H("Common translation of phases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At row i, shiftPhases c t subtracts a_i times t.1 plus b_i times t.2 from c i. The same t is used for every row."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-phasedomain"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.phaseDomain"),
                H("Canonical phase domain sizes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seven sizes are 1,1,2,2,4,6,1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-canonical"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.Canonical"),
                H("Canonical base phases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each of the first seven rows, the integer remainder of its assigned phase modulo its original modulus is less than its corresponding phaseDomain size."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-0"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.rows"),
                H("Original rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Seven base rows followed by the remaining 245 original rows. The modulus-11 row labelled by prime 23 is retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203rows-1"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Rows.hits"),
                H("Original congruence events"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer linear form is compared with a fixed original phase modulo the row modulus."))),
                DescribeRole.Definition)),
        []));
}
