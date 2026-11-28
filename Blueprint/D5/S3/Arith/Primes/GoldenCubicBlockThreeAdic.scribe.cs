using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockThreeAdicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native cubic Lucas trajectory at three is an exact transient toward the fixed residue one.",
        H("The three-adic transient of cubic Lucas blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-three-adic-depth"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_depth"),
                H("Exactly one digit of convergence at each step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The valuation of the level-i block minus one is exactly i+1, "
                    + "including the initial level i=0. The shifted recurrence factors "
                    + "into the current deviation and a multiplier of valuation one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-three-adic-lag"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_lag"),
                H("The earlier level controls the entire lag valuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The difference between levels n and m, for n>m, has valuation m+1. "
                    + "This depends on where the two readings start, not on the lag."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-three-adic-transient"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_clamped_phase"),
                H("Exact pairwise collisions in the finite transient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At precision a, two levels collide exactly when their indices "
                    + "agree after clamping at a-1. Every earlier residue is distinct, "
                    + "and every later residue is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-three-adic-no-period"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_no_initial_period"),
                H("No positive period through the initial reading at nontrivial precision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At precision greater than one, no positive shift preserves all readings "
                    + "starting at level zero. The eventual fixed tail is distinct from periodicity "
                    + "of the entire trajectory."))),
                DescribeRole.Theorem))));
}
