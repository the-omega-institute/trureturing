using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.TraceFibers;

internal sealed class ThreeActionModulusEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed Fibonacci fiber interface gives the scalar envelopes of the two "
            + "distinguished three-action continuations, together with the finite word shapes.",
        H("Three Action Modulus Envelope"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-action-modulus-envelope"),
            DeclarationHandle.Create("D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope.three_action_modulus_envelope"),
            H("Three-action scalar envelope"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For words of length at most three in the advance and exchange actions, "
                        + "the pair consisting of the diagonal difference and lower-left entry "
                        + "has the seven listed values.")),
                Paragraph(Text(
                    "For a positive rank-one fiber with x=(k+h)r, the frozen fixed-fiber "
                        + "modulus theorem applied to MJM and M^3 gives the scalar suprema "
                        + "with parameters (2-h,1) and (2-2h,2), respectively.")),
                Paragraph(Text(
                    "The quadratic separation functions satisfy phi_A(d)-phi_S(d)="
                        + "d(d/r-h); their common spacing is rh and their common tolerance is 2rh. "
                        + "The threshold values are ordered as 0<2rh<(k+2)x<2(k+1)x."))),
            DescribeRole.Theorem))));

}
