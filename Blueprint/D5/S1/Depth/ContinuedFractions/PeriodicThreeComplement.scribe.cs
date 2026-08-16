using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class PeriodicThreeComplementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The period-three continued-fraction tail and its [0;1,2] prefix are complementary.",
        H("Periodic Three Complement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("periodic-three-continued-fraction-complement"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/PeriodicThreeComplement."
                    + "periodic_three_continued_fraction_complement"),
                H("The period-three tail has an exact complementary prefix"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("x"), Eq, Frac,
                    Grp(Sqrt, Grp(D(1, 3)), Minus, D(3)), Grp(D(2)), Comma, Quad, Sp,
                    Operatorname, Grp(F.Id("CF")), Open, F.Id("x"), Close, Eq,
                    OpenBracket, D(0), Semi, Overline, Grp(D(3)), CloseBracket,
                    Comma, Quad, Sp,
                    Frac, Grp(D(1)),
                    Grp(D(1), Plus, Frac, Grp(D(1)), Grp(D(2), Plus, F.Id("x"))),
                    Plus, F.Id("x"), Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let x=(sqrt(13)-3)/2. Its floor is zero, and the inverse of its "
                    + "fractional part is 3+x. Mathlib's of_h_eq_floor, of_s_head, and "
                    + "of_s_succ recurrences therefore compute every continued-fraction "
                    + "coefficient after the head as 3. The same quadratic fixed-point "
                    + "identity reduces the [0;1,2] prefix to 1-x.")),
                Paragraph(Text(
                    "This declaration closes only the continued-fraction identity in residual "
                    + "remark/27.447-27.450. The subsequent lambda=4 accumulation claim, the "
                    + "647-word survey, and the stated derived-set candidates remain outside "
                    + "this formalization."))),
                DescribeRole.Theorem))));
}
