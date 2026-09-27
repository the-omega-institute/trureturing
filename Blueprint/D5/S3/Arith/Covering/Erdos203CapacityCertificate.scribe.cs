using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class Erdos203CapacityCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic polynomial encoding certifies actual histogram bounds on the 8640-point six-row transversal. The soundness theorem connects typed arithmetic certificates to all 245 original tail rows; 96 explicit certificates supply every canonical class.",
        H("Sound certificates for original-residue capacities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-packed"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.packed"),
                H("Packed actual histogram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum over q in U of 16384 raised to originalResidue i q encodes the original-residue bucket counts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-keep"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.keep"),
                H("Six-row exclusion predicate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Boolean predicate excludes the six original forms at canonical phases 0,0,c/48,c/24 modulo 2,c/6 modulo 4,c modulo 6."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-canonicalphases"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.canonicalPhases"),
                H("Canonical seven-phase vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a class in Fin 96, the first seven phases are 0,0,c/48,c/24 modulo 2,c/6 modulo 4,c modulo 6,0. Tail phases in this representative are zero; the capacity bound allows arbitrary actual tail phases."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-encodepolynomials"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.encodePolynomials"),
                H("Cyclic histogram projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each horizontal polynomial, reduction modulo 16384 to the power g minus one collects x modulo g. Digit extraction and remapping by a t + b y modulo g form the packed projected histogram."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-key"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.key"),
                H("Distinct restricted row queries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal 129 triples give the restricted gcd and the two original coefficient residues for every distinct tail query."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-tailindex"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.tailIndex"),
                H("Original tail index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Tail index j is 7+j in Fin 252."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-rowkey"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.rowKey"),
                H("Original row to query map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of the 245 original tail rows is assigned its index in the 129-query table. The soundness proof checks the restricted gcd and both coefficient residues."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-weight"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.weight"),
                H("Scaled original-row capacity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weight is the factor 11 for labels 199 and 2377 or 10 otherwise, multiplied by the restricted gcd and period divided by the original modulus."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-0"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.CapacityCertificate"),
                H("Typed capacity certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The certificate carries 24 horizontal encodings, 129 shared residue histograms, histogram bounds and an uncovered-point count. Its proof fields require equality with the actual six-row predicate, the cyclic encoding equations, every digit bound, the count equation and the exact scaled deficit inequality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203capacitycertificate-1"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203CapacityCertificate.certificate_bound"),
                H("Soundness for actual finite histograms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every class c in Fin 96 and every CapacityCertificate c, the actual histogram maxima satisfy the scaled gap inequality with numerator 41512904387 and denominator 2792167686000. Base-16384 digit extraction equals filtered Finset cardinality because each histogram has at most 8640 points. Cyclic polynomial reduction preserves the residue counts, and every original tail row is mapped to its checked restricted gcd and coefficient residues. This theorem alone has a certificate parameter; the final result discharges it for all 96 classes."))),
                DescribeRole.Theorem)),
        []));
}
