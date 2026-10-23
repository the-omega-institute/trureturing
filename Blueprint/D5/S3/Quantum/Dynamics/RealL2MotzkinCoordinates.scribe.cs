using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class RealL2MotzkinCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Dynamics/RealL2MotzkinCoordinates.iterate_coordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coordinate of every real half-line iterate is an alternating-sign "
            + "evaluation of the boundary-weighted Motzkin polynomial.",
        H("Real Half-Line Motzkin Coordinates"),
        Blocks(Describe.Lean(
            DescribeId.Create("real-l2-motzkin-coordinates"),
            DeclarationHandle.Create(Declaration),
            H("The coordinate correspondence at every natural order and height"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let H be the complete real Hilbert space of square-summable sequences "
                        + "indexed by the natural numbers. Write e_j for its coordinate vectors "
                        + "and S for its unilateral shift, with S e_j = e_(j+1). "
                        + "Set K_infinity = 3I-S-S*, using the Hilbert adjoint of this actual "
                        + "shift. The endpoint is e_0. Natural coordinate j corresponds to "
                        + "coordinate j+1 on the positive-integer half-line.")),
                Paragraph(Text(
                    "Let M_(k,j)(t,s) be the existing integer-coefficient Motzkin polynomial: "
                        + "up and down steps have weight one, and horizontal steps have weight "
                        + "s at height zero and t at positive height. The expression "
                        + "M_(k,j)(3,3) means the ring-homomorphic evaluation that sends every "
                        + "integer coefficient to its real cast and both variables to the "
                        + "real number three.")),
                Paragraph(Text(
                    "Pairing S with coordinate vectors shows that (S* x)_j = x_(j+1). "
                        + "Thus the zeroth coordinate of K_infinity x is 3x_0-x_1; "
                        + "at positive coordinate j+1 it is 3x_(j+1)-x_j-x_(j+2). "
                        + "Induction on k matches these identities with the last-step "
                        + "Motzkin recurrence. The factor (-1)^j turns both negative "
                        + "neighbor terms into the two positive path contributions.")),
                Paragraph(Text(
                    "At k=0 the equality is the endpoint coordinate identity, including "
                        + "j=0 and every positive j. The equality also includes every j>k, "
                        + "where the Motzkin polynomial and the iterate coordinate vanish. "
                        + "No finite truncation or bound on the power or coordinate is used."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("k"), j = F.Id("j");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula endpoint = Seq(F.Id("e"), Underscore, Grp(D(0)));
        Formula power = Seq(F.Id("K"), Underscore, Grp(Infty), Caret, Grp(k));
        Formula coordinate = Seq(Open, power, Sp, endpoint, Close, Underscore, Grp(j));
        Formula evaluation = Seq(F.Id("M"), Underscore, Grp(k, Comma, j),
            Open, D(3), Comma, D(3), Close);
        return Disp(Seq(
            Forall, Sp, k, Comma, j, Sp, InMacro, Sp, nat, Comma, Sp,
            coordinate, Sp, Eq, Sp,
            Open, Minus, D(1), Close, Caret, Grp(j), Sp, evaluation, Dot));
    }
}
