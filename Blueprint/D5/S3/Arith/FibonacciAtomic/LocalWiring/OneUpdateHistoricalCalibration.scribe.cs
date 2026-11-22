using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class OneUpdateHistoricalCalibrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/FibonacciAtomic/LocalWiring/OneUpdateHistoricalCalibration.";

    private static Formula P => F.Id("p");
    private static Formula Cherries => Call("C", F.Id("S"));
    private static Formula Site => Seq(P, Sp, InMacro, Sp, Cherries);
    private static Formula Length => Seq(Lvert, Sp, P, Rvert, Plus, D(2));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual update and the paid presence bits below the old terminal forks recover "
        + "the full old labelled tree and its local address adapter. The three literal Read "
        + "prices are jointly sharp, while the newest state retains independent hidden choices.",
        H("Sharp historical calibration after one actual update"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gpo-one-update-paid-historical-calibration"),
                DeclarationHandle.Create(Prefix + "exact_one_update_calibration"),
                H("One actual update calibrates the preceding physical boundary"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("U"), Underscore, Grp(F.Id("updates")), Eq, D(1), Quad, Sp,
                    F.Id("Q"), Eq, Lvert, Sp, Cherries, Rvert, Quad, Sp,
                    F.Id("W"), Eq, Sum, Underscore, Grp(Site), Open, Length, Close, Quad, Sp,
                    F.Id("M"), Underscore, Grp(F.Id("addr")), Eq, Max, Underscore, Grp(Site),
                    Open, Length, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The fixed old shape S has already been acquired at an attained horizon n≥2 "
                        + "from the known alpha seed. On the same source, execute one actual Step. "
                        + "There are no reads before this update in the attaining program. After it, "
                        + "for each old cherry address p read the literal absolute word paa once. "
                        + "Its actual Boolean presence reply equals the old left-beta bit at p.")),
                    Paragraph(Text(
                        "The program uses just the retained shape and the paid reply list to decode "
                        + "the entire old labelled physical tree; its offline finite enumeration "
                        + "is not charged as a source Read. It recovers the old local semantic L/R "
                        + "adapter by comparing the children's local growth ages and composing "
                        + "the resulting persistent frames. This does not access a past register.")),
                    Paragraph(Text(
                        "Q counts occurrences, including repetitions and absence. W sums the full "
                        + "absolute lengths without a discount for shared prefixes. M is the longest "
                        + "such word. For every correct finite adaptive protocol with this same acquired "
                        + "shape, no supplementary old-label information, and exactly one update, "
                        + "all three inequalities hold on the same individual run. Pre-update reads "
                        + "are permitted and charged, but cannot distinguish a single old cherry flip.")),
                    Paragraph(Text(
                        "For the fixed old labelled state, its beta leaf sites are exactly the new "
                        + "cherry addresses, and there are F_n of them. Every Boolean assignment "
                        + "to these sites occurs in exactly one legal successor, giving 2^F_n "
                        + "successors with identical presence replies at every physical word. "
                        + "The result does not price the earlier acquisition of S, local computation, "
                        + "or a protocol with additional actual updates."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
