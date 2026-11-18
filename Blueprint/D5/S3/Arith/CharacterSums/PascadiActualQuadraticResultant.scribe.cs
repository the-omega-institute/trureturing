using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiActualQuadraticResultantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quadratic LQ pencil has a seventh-power height criterion, including degenerate leading baselines.",
        H("Removing the quadratic eighth-power height loss"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-quadratic-pencil-seventh-weight-resultant-zero"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiActualQuadraticResultant.actual_quadratic_pair_resultant_zero"),
                H("The complete actual quadratic branch"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the existing pair l m q r s i = L0*Qi-Li*Q0 for three actual coefficient rows. Suppose I,J>=1 and |li|<=3I, |mi|<=3J, |qi|<=I squared, |ri|<=2IJ, |si|<=J squared. Both actual pair polynomials have degree two, value divisible by p cubed and derivative divisible by p at the same integer beta. The first leading coefficient is nonzero modulo p, and L0(beta) is a unit. If 14256*(IJ) to the seventh power is less than p to the fifth power, their padded quadratic resultant is zero.")),
                    Paragraph(Text("The vanishing cubic coefficients force all leading pairs (mi,si) onto one primitive integer direction whenever the baseline pair is nonzero. Cancel the baseline unit factor from the exact resultant before applying the cofactor height bound. If both baseline leading entries vanish, cancel the constant baseline from the explicit integer quotient and use its seventh weighted height. These two branches include secondary coordinates zero, the anchor coordinate, and constant secondary sums; none is silently excluded.")),
                    Paragraph(Text("The cofactor elimination route was suggested through the oracle broker. Codex derived the explicit resultant factorization, the short unit-cancellation identity, and the constant-baseline quotient, then implemented the complete branch split. The existing p-fifth divisibility and resultant definitions are reused. No worldwide novelty or method-priority claim is made.")),
                    Paragraph(Text("This theorem removes a height obstruction for the actual degree-two branch. Extending the original six-return count additionally requires stronger localized factors for genuine cubic inputs, the residual cubic bound, updated algebraic heights, and the full counting assembly. The unrestricted arbitrary-modulus conjecture remains open."))),
                DescribeRole.Theorem))));
}
