using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class PeritoUnitCircleSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum of distances from a unit complex phase to the negatives of the regular d-th roots is at most twice the cosecant of pi over twice d.",
        H("A Regular Unit-Circle Sum Bound"),
        Blocks(
            Paragraph(Text(
                "Let d be an integer at least two and let omega be exp(2 pi i / d). " +
                "For a complex number z of modulus one, consider the sum of |1 + omega^y z| " +
                "over y from zero to d minus one.")),
            Describe.Lean(
                DescribeId.Create("the-regular-unit-circle-distance-sum-bound"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/PeritoUnitCircleSum.unit_circle_sum_le"),
                H("The distance sum is bounded uniformly in the phase"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(2), Le, Sp, F.Id("d"), Rightarrow, Sp,
                    Forall, Sp, F.Id("z"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Vert, Sp, F.Id("z"), Vert, Eq, D(1), Rightarrow, Sp,
                    Sum, Underscore, Grp(F.Id("y"), Eq, D(0)), Caret, Grp(F.Id("d"), Minus, D(1)),
                    Vert, D(1), Plus, F.Id("omega"), Caret, Grp(F.Id("y")), F.Id("z"), Vert,
                    Le, Frac, Grp(D(2)), Grp(Sin, Open, Frac, Grp(Pi), Grp(D(2), F.Id("d")), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write z as exp(2 i s). Factoring 1 + exp(2 i t) as " +
                        "2 cos(t) exp(i t) shows that the distance sum is " +
                        "twice the sum of |cos(s + pi y / d)|.")),
                    Paragraph(Text(
                        "This absolute cosine sum has period pi / d: shifting the phase " +
                        "cycles the sample indices, and the last sample differs from the " +
                        "first by pi, which preserves the absolute cosine. Reduce s modulo " +
                        "this period to t in [-pi/2, -pi/2 + pi/d). All d sampled angles " +
                        "then lie in [-pi/2, pi/2], where cosine is nonnegative.")),
                    Paragraph(Text(
                        "The finite trigonometric sum identity gives the cosine sum as " +
                        "cos(t + (d - 1) pi / (2 d)) / sin(pi / (2 d)). " +
                        "The denominator is positive and cosine is at most one, giving " +
                        "the stated uniform bound. The same reduction applies to both " +
                        "odd and even values of d."))),
                DescribeRole.Theorem))));
}
