using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockTailOrbitImageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cubic Lucas tail fills exactly a disjoint collection of full residue fibres at every precision above the first nonconstant period plateau.",
        H("The complete residue image of a cubic Lucas tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-full-phase-image"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_phase_image"),
                H("A single phase fills its entire residue fibre"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let h be the seed-block depth, e the base-three Fermat depth, and t "
                    + "the order of nine modulo the seed prime p. Above precision 2h+e, "
                    + "each index phase r modulo t fills every lift of its coarse residue. "
                    + "At an added k digits, the first p^k samples in that phase suffice."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-total-image"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_total_image"),
                H("The orbit is a union of full fibres"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An integer occurs at the finer precision if and only if its coarse "
                    + "residue is one of the first t samples. This describes image membership "
                    + "and not merely a recurrence period."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-phase-disjoint"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_phases_disjoint"),
                H("The phase fibres are pairwise disjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first t coarse samples are distinct. Thus each observed fine residue "
                    + "belongs to exactly one of the listed phase fibres."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-one-cycle-residues"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_one_cycle"),
                H("A unique index in one period represents each residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite orbit has exactly t times p^k residues at the added k digits."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-nineteen-image"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_nineteen_image"),
                H("Nine explicit coarse residues determine the entire first-prime image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the first block prime 19, every higher-precision lift comes from "
                    + "one of nine exact residues modulo 6859. Their values are computed "
                    + "from the cubic recurrence without evaluating large Lucas numbers."))),
                DescribeRole.Theorem))));
}
