using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.RawObservation;

internal sealed class ShiftReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Determine precisely what current and shifted integer displays recover about an actual raw input.",
        H("Integer Displays under Actual Raw-Digit Shifts"),
        Blocks(
            Paragraph(Text(
                "shiftedValue(k,r) evaluates the existing shiftDigits(k,r) using rawValue. "
                + "The shift is applied to the original raw input, without first substituting "
                + "its canonical normal form. Its value is the phi coefficient of phi^k times "
                + "the existing betaDigits(r). This commuting identity gives the displays their "
                + "mathematical meaning.")),
            Describe.Lean(
                DescribeId.Create("raw-admissible-display-pair"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/ShiftReadout.display_pair_iff"),
                H("Exactly which two displays can come from one raw input"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("DisplayPairs"), Sp, Eq, Sp, OpenBrace,
                    Open, F.Id("n"), Comma, F.Id("m"), Close, Sp, Colon, Sp,
                    D(3), F.Id("n"), Sp, Leq, Sp, D(2), F.Id("m"), Sp, Land, Sp,
                    F.Id("m"), Sp, Leq, Sp, D(2), F.Id("n"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both coordinates are natural numbers. For the actual golden image a+n*phi, "
                    + "the shifted readout is m=a+n. The exact raw-image cone becomes 3n<=2m "
                    + "and m<=2n. Conversely the two-slot representative realizes every such "
                    + "pair, so these are sufficient as well as necessary conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-shift-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/ShiftReadout.reconstruct_beta"),
                H("Recover the actual golden image"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("beta"), Open, F.Id("r"), Close, Sp, Eq, Sp,
                    Open, F.Id("m"), Sp, Minus, Sp, F.Id("n"), Close,
                    Sp, Plus, Sp, F.Id("n"), F.Id("phi")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here n is rawValue(r) and m is shiftedValue(1,r). The inverse formula "
                    + "recovers betaDigits(r), not r itself. A value m calculated from an "
                    + "arbitrarily chosen representative of n is not an additional observation "
                    + "of an unknown input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-all-shifts-semantic-kernel"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/ShiftReadout.beta_eq_iff_all_shifts"),
                H("All shifts distinguish exactly the golden semantic classes"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("ker"), Open, F.Id("allShifts"), Close,
                    Sp, Eq, Sp, F.Id("ker"), Open, F.Id("beta"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal golden images give every shifted readout equal. Conversely the "
                    + "zero and one shifts recover both integral coordinates. The source also "
                    + "proves the exact Fibonacci recurrence for these actual shift values. "
                    + "Thus arbitrary many shift observations do not secretly recover more "
                    + "raw-expression information than the first two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-single-display-sufficiency"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/ShiftReadout.display_determines_beta_iff"),
                H("A single display suffices only at zero and one"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("SufficientDisplays"), Sp, Eq, Sp,
                    OpenBrace, D(0), Comma, D(1), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural n>=2, actual raw inputs produce the same display n "
                    + "and two distinct one-shift readings, 2n and 2n-1. At n<=1 the cone "
                    + "contains just one first coordinate. The statement is relative to the "
                    + "existing nonnegative raw-input domain, not an intrinsic hidden state "
                    + "assigned to every integer."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/RawObservation/RealizableFiber")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/Admissibility/LeastDigitDecomposition")),
        ]));
}
