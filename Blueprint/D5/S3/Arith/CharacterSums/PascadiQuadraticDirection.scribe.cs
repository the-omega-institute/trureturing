using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiQuadraticDirectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common integer direction in the leading coefficient data gives a sharper quadratic singular resultant gap.",
        H("Quadratic pencils with a common leading direction"),
        Blocks(
            Describe.Lean(DescribeId.Create("quadratic-direction-resultant-zero"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiQuadraticDirection.quadratic_direction_resultant_zero"),
                H("Cancel the baseline factor before comparing heights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take three integer coefficient rows with linear polynomials Li=li+d*ki*T and quadratic polynomials Qi=qi+ri*T+n*ki*T^2. Let Pi=L0*Qi-Li*Q0 for i=1,2. Assume both Pi have degree two, vanish modulo p cubed at the same integer b, and have derivative zero modulo p there. The leading coefficient of P1 remains nonzero modulo p and L0(b) is a unit. If the actual coefficient bounds are |qi|<=I^2, |ri|<=2IJ, |li|<=3I, |ki|<=D, with nonnegative I,J,D, |d|D<=3J, |n|D<=J^2 and D<=3J^2, then 6804*I^6*J^4<p^5 forces the actual padded quadratic resultant of P1,P2 to vanish.")),
                    Paragraph(Text("The three by four coefficient matrix has rows (qi,ri,li,ki). Its signed maximal minors satisfy the cofactor quadratic G=z0*z3-d*z1*z2-n*z1^2. An exact polynomial identity factors the resultant as -F0*G, where F0=d^2*k0*q0-d*l0*r0+n*l0^2. A second identity gives (l0*k1-l1*k0)*F0=P1.coeff(2)*L0(b)^2-m0*L0(b)*P1'(b)+m0^2*P1(b), with m0=d*k0. The modular root and derivative conditions therefore make F0 a unit, without assuming that d or k0 is a unit. The existing fifth-power quadratic resultant divisibility descends to G. The four minor bounds give |G|<=6804*I^6*J^4, so G and the resultant are zero.")),
                    Paragraph(Text("The cofactor construction was suggested during a Pro research consultation; Codex independently checked its degeneracies and derived the explicit resultant and unit-cancellation identities. The theorem allows zero direction coordinates and zero row multipliers. It supplies the common-direction step only: it does not construct the integer direction from original endpoint rows, count the resulting common-factor fibers, settle the full arbitrary-modulus conjecture, or assert literature priority."))),
                DescribeRole.Theorem))));
}
