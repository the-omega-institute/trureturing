using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class MarkedPrimeWordSnapshotFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime words over a strict divisor snapshot.",
        H("Marked prime words and divisor snapshots"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("marked-prime-word-snapshot-fiber-equivalence"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MarkedPrimeWordSnapshotFiber.snapshot_fiber_equiv_and_forced_marks"),
                H("Splitting into successive quotient words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a strict divisor chain from one to an integer greater than one. "
                    + "A prime word together with marks realizing its prefix products is equivalent "
                    + "to a family of prime words, one for each successive quotient of the chain. "
                    + "Splitting at the marks gives the family; concatenation reconstructs the word. "
                    + "Each mark is forced to equal the total prime multiplicity of its observed divisor."))),
                DescribeRole.Theorem))));
}
