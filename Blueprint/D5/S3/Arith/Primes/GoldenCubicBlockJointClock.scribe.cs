using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockJointClockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two primes observing the same Lucas tail have a precise shared-time constraint.",
        H("Synchronous prime clocks in one Lucas tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-joint-clock-existence"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicBlockJointClock.synchronous_pair_exists"),
                H("Exact compatibility of two prime clocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two separately observed residues occur together at a single later block exactly when their time labels agree modulo the gcd of the individual periods."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-joint-clock-collision"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicBlockJointClock.synchronous_pair_collision"),
                H("The joint clock has the lcm kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two block indices give the same pair of residues precisely when their difference is a multiple of the lcm of the periods. The initial offset may be chosen after both prime witnesses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-joint-clock-pairs"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicBlockJointClock.compatibleResiduePairs"),
                H("Enumerating the compatible residue pairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Time labels below the lcm biject with precisely the compatible pair labels, including when the periods are not coprime."))),
                DescribeRole.Definition))));
}
