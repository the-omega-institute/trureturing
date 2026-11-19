using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class PositiveEnergyPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure positive-energy coordinates and their ordinary partition equivalence.",
        H("Positive Energy Partition Coordinates"),
        Blocks(
            Paragraph(Text("This common G dependency contains the pure finite-support "
                + "positive-energy coordinate construction reused by the ordinary coloured "
                + "occupation bridge and by the concrete polynomial Fock consumers. The "
                + "public declaration namespaces remain those of the original consumers.")),
            Describe.Lean(
                DescribeId.Create("positive-energy-partition-energy"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.energy"),
                H("Positive weighted energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An exponent vector assigns the positive weight "
                    + "i + 1 to the variable indexed by i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-energy-partition-energy-fiber"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.EnergyFiber"),
                H("Fixed positive-energy exponent fibres"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("EnergyFiber N is the subtype of finitely supported "
                    + "natural exponent vectors whose positive weighted energy is N, "
                    + "including the zero-energy fibre."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-energy-partition-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.energyFiberEquivPartition"),
                H("Positive-energy fibres are ordinary integer partitions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every N, the positive weighted exponent "
                    + "vectors are equivalent to Nat.Partition N. The forward map "
                    + "repeats i + 1 according to the exponent at i, and predecessor "
                    + "decoding is inverse on positive partition parts."))),
                DescribeRole.Theorem)
        )));
}
