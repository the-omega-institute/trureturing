using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.TraceFibers;

internal sealed class ThreeActionModulusEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar inverse modulus for a fixed upper-shear history has an exact "
            + "three-action envelope whose optimal continuation depends on tolerance.",
        H("Three Action Modulus Envelope"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-action-modulus-envelope"),
            DeclarationHandle.Create("D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope.three_action_modulus_envelope"),
            H("The complete scalar envelope"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix an actual upper-shear prefix U^k with k at least one and "
                        + "positive fiber parameters x=(k+h)r, where 0<h<1. A candidate "
                        + "is a chronological continuation with at most three advance "
                        + "or exchange actions whose third trace read is injective on "
                        + "the entire open positive source fiber.")),
                Paragraph(Text(
                    "The fifteen words have seven coefficient shapes. Exactly the "
                        + "shapes (1,1), (2,1), and (2,2) are injective. The last two "
                        + "are attained only by S=MJM and A=M^3. Their stability "
                        + "margins are 2-h and 2-2h, and their lower-left entries "
                        + "are one and two, respectively. Every word of shape (1,1) "
                        + "has the same scalar modulus as M.")),
                Paragraph(Text(
                    "The exact moduli are the positive quadratic inverse roots "
                        + "capped at x. The endpoint separation functions satisfy "
                        + "phi_A(d)-phi_S(d)=d(d/r-h), so their inverse order reverses "
                        + "at spacing rh and tolerance 2rh. The saturation thresholds "
                        + "obey 0<2rh<(k+2)x<2(k+1)x.")),
                Paragraph(Text(
                    "At zero tolerance both distinguished moduli are zero. For "
                        + "0<tau<2rh, S is the unique optimum. At tau=2rh, exactly S "
                        + "and A attain the minimum rh. For 2rh<tau<2(k+1)x, A is "
                        + "the unique optimum, including the interval where S has "
                        + "already saturated. At and above 2(k+1)x every injective "
                        + "candidate has modulus x. Consequently no single candidate "
                        + "is optimal for every tolerance.")),
                Paragraph(Text(
                    "All comparisons retain the same executed prefix and source "
                        + "fiber. They concern alternative continuations selected "
                        + "before the third read and do not combine observations "
                        + "from different futures."))),
            DescribeRole.Theorem))));
}
