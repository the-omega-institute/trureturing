using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedBIntegerClockDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The perturbed integer clock has a unique large root within one of its unperturbed reference.",
        H("Large roots of the exact fixed-perturbation integer clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inverse-clock-eq-iff"),
                DeclarationHandle.Create(Gid + ".inverseClock_eq_iff"),
                H("Equivalence with the exact price equation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every nonnegative integer height and positive price, the logarithmic inverse clock "
                    + "equals that height precisely when the perturbed price equals the target price. "
                    + "The target uses the integer exponent and the literal subtraction by two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-fixed-b-integer-clock"),
                DeclarationHandle.Create(Gid + ".exists_fixedB_integerClock"),
                H("The large roots exist and diverge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unperturbed clock is the positive inverse of the continuous strictly increasing map "
                    + "L to L times exp L at the corresponding reciprocal price. With a fixed real perturbation "
                    + "and positive decay exponent, the relative price factor tends to one. This brackets all "
                    + "late roots within one of the unperturbed clock, and the normalized price derivative "
                    + "is eventually negative, giving uniqueness beyond a fixed positive threshold."))),
                DescribeRole.Theorem))));
}
