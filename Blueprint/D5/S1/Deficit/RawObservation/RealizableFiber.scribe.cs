using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.RawObservation;

internal sealed class RealizableFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classify the states that actually arise under the existing raw Fibonacci evaluator.",
        H("The Realizable Fiber of an Integer Display"),
        Blocks(
            Paragraph(Text(
                "The carrier is the existing RawDigits of finite nonnegative multiplicities. "
                + "Its golden evaluation is the existing betaDigits, and its displayed natural "
                + "number is rawValue. The public betaDigits_b theorem links these two evaluations. "
                + "No unrestricted integer coordinate is appended to a displayed number.")),
            Describe.Lean(
                DescribeId.Create("raw-golden-exact-image"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/RealizableFiber.raw_image_iff"),
                H("The image is exactly an integral cone"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("RawGoldenImage"), Sp, Eq, Sp, OpenBrace,
                    Open, F.Id("a"), Comma, F.Id("b"), Close, Sp, Colon, Sp,
                    D(0), Sp, Leq, Sp, F.Id("a"), Sp, Land, Sp,
                    F.Id("a"), Sp, Leq, Sp, F.Id("b"), Sp, Land, Sp,
                    F.Id("b"), Sp, Leq, Sp, D(2), F.Id("a"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every golden generator phi^(i+2) lies in this cone, and nonnegative "
                    + "linear combinations preserve it. Conversely, a point (a,b) in the cone "
                    + "is realized with 2a-b copies of the first slot and b-a copies of the "
                    + "second slot. Both coefficients are nonnegative integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-display-fiber"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/RealizableFiber.display_fiber_iff"),
                H("A display n leaves exactly a finite interval of golden coordinates"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("FiberCoordinates"), Open, F.Id("n"), Close,
                    Sp, Eq, Sp, OpenBrace, F.Id("a"), Sp, Colon, Sp,
                    F.Id("a"), Sp, Leq, Sp, F.Id("n"), Sp, Land, Sp,
                    F.Id("n"), Sp, Leq, Sp, D(2), F.Id("a"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a fixed natural display n, every integer a in the displayed interval "
                    + "and only such an a comes from an actual raw input. This is the interval "
                    + "from ceiling(n/2) through n, not the entire integer fiber of GoldenInt. "
                    + "The theorem classifies golden images; it does not count all raw expressions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-two-slot-realization"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/RealizableFiber.two_slot_representation"),
                H("Every golden image has an explicit two-slot representative"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("beta"), Open, F.Id("twoSlot"), Open, F.Id("r"), Close, Close,
                    Sp, Eq, Sp, F.Id("beta"), Open, F.Id("r"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The construction preserves the actual golden evaluator. The two slot "
                    + "multiplicities are unique for that evaluator, but replacing the original "
                    + "raw expression by them need not preserve canonicality or available carry moves."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/DoubleFaceLength")),
        ]));
}
