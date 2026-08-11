using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class SuccessorCarryTerminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Recurrence/SuccessorCarryTermination",
            "Zeckendorf successor carry positions are bounded by the highest Fibonacci index."),
        H("Zeckendorf Successor Carry Termination"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("zeckendorf-successor-carry-chain-terminates"),
                H("The successor carry chain terminates within the highest index"),
                LeanTheorem(
                    "D5/S1/Recurrence/SuccessorCarryTermination.successor_carry_chain_terminates"),
                Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("card")), Open,
                    F.Id("Carry"), Open, F.Id("n"), Close, Close,
                    Sp, Leq, Sp,
                    Operatorname, Grp(F.Id("greatestFib")), Open, F.Id("n"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Increment a natural number and compare its two canonical Zeckendorf "
                        + "representations. The successor carry positions are exactly the occupied "
                        + "Fibonacci indices present before the increment and absent afterward. "
                        + "Their number is bounded by the greatest Fibonacci index of the original "
                        + "number, so propagation cannot continue beyond the highest occupied scale. "
                        + "A companion theorem checks that the Fibonacci weight removed by these "
                        + "positions, plus one, equals the weight introduced by normalization; this "
                        + "makes the finite trace an arithmetic carry certificate rather than only a "
                        + "set-theoretic difference.")),
                    Paragraph(Text(
                        "The pinned library was searched before proving. It provides the canonical "
                        + "Zeckendorf representation, exact decoding by Fibonacci summation, its "
                        + "successor unfolding, and the two-index descent of each greedy tail. It has "
                        + "no declaration bounding a successor carry trace or even the length of a "
                        + "canonical representation by its greatest Fibonacci index. The deposited "
                        + "proof derives that length bound by strong induction through the library's "
                        + "tail descent and then transfers it to the carry-position subset. This is a "
                        + "new proof over library primitives, not a thin wrapper and not a duplicate "
                        + "of the general local normalizer already present in the repository.")))
            ))));
}
