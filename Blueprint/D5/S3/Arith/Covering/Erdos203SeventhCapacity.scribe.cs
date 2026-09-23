using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class Erdos203SeventhCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original seventh row is x+8y=0 modulo 11. Its removal leaves exactly ten elevenths of every selected union of six-row kernel cosets. The corresponding capacity factor is ten elevenths for all tail rows except the parallel rows labelled 199 and 2377.",
        H("The seventh original row and conditional capacities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203seventhcapacity-seventh"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventh"),
                H("Seventh original form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The homomorphism originalMap 6 takes values in ZMod 11."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203seventhcapacity-eleveninverse"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SeventhCapacity.elevenInverse"),
                H("Explicit inverse residues"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer list 0,1,6,4,3,9,2,8,7,5,10 is indexed by the argument modulo 11; it gives multiplicative inverses at every nonzero residue."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203seventhcapacity-elevenwitness"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SeventhCapacity.elevenWitness"),
                H("Preserving translation witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the original modulus is divisible by 11, the translation is an integer multiple of (8640 b,-8640 a). Otherwise it is a multiple of (360 e,0). The multiplier is chosen using elevenInverse; the theorem verifies its exact row constraints."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203seventhcapacity-seventhfactor"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventhFactor"),
                H("Original-row capacity factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The factor is 11 for prime labels 199 and 2377 and 10 for every other row."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203seventhcapacity-0"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SeventhCapacity.sevenRegion"),
                H("Region missed by the seventh row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The region consists of points in the selected six-row cosets whose seventh original linear form is nonzero modulo 11."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203seventhcapacity-1"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventh_capacity"),
                H("Exact density and compatible original-row bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every subset U of the 360 by 24 transversal, 11 times 8640 times the region cardinality equals 10 times the cardinality of U times M squared. For every one of the 245 tail rows and every phase in its original modulus, the intersection satisfies the six-row histogram bound multiplied by ten elevenths; the factor is one for labels 199 and 2377. Explicit integer translations preserve the six-row kernel and the original row fiber while cycling the seventh residue. This establishes compatibility on the same actual torus and phase, including nonprimitive restrictions."))),
                DescribeRole.Theorem)),
        []));
}
