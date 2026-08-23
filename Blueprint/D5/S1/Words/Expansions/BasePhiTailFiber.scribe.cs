using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Expansions;

internal sealed class BasePhiTailFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty complete negative base-phi tail of a positive natural has a singleton or three-consecutive fiber.",
        H("Complete Negative Base-Phi Tail Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("negative-tail-fiber-shape"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiTailFiber.negative_tail_fiber_shape"),
                H("Complete negative tails have the singleton-trident dichotomy"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("d"), Underscore, Grp(Minus, D(1)), Eq, D(1), Sp,
                    Rightarrow, Sp, F.Id("F"), Underscore, F.Id("N"), Eq,
                    OpenBrace, F.Id("N"), CloseBrace, Comma, Esc,
                    F.Id("d"), Underscore, Grp(Minus, D(1)), Eq, D(0), Sp,
                    Rightarrow, Sp, Exists, Bang, Sp, F.Id("q"), Comma, Esc,
                    F.Id("F"), Underscore, F.Id("N"), Eq, OpenBrace,
                    F.Id("q"), Comma, F.Id("q"), Plus, D(1), Comma,
                    F.Id("q"), Plus, D(2), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a positive natural whose canonical expansion reaches a negative exponent, "
                        + "the complete negative-position digit tail determines that natural uniquely "
                        + "when its first digit is one. When the first digit is zero, the same tail occurs "
                        + "at exactly three consecutive positive naturals, with a unique least member.")),
                    Paragraph(Text(
                        "This is the singleton-trident consequence of Dekking's recursive structure "
                        + "used by the frontier theorem. It is deliberately narrower than a formalization "
                        + "of the paper's complete recursive word presentation."))),
                DescribeRole.Theorem))));
}
