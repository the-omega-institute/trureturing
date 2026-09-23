using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.PhysicalDivider;

internal sealed class HistoriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One finite-control divider on sixteen sequential bit tapes supports arbitrary finite "
        + "same-capacity call histories while preserving the caller's tapes and retained storage extents.",
        H("Framed Physical Division"),
        Blocks(
            Paragraph(Text(
                "Let X be the set of tuples x = (w,a,d,capacity,oldQ,oldR,caller,frame) "
                + "with natural w,a,d, Boolean lists capacity,oldQ,oldR, a map caller from "
                + "CallerTape to Boolean tapes, and a map frame from CallerTape to Extent. "
                + "Membership requires 1 <= w, a < 2^w, 0 < d < 2^w, length(capacity) = w, "
                + "length(oldQ) <= w, length(oldR) <= w+1, and Within(caller(j),frame(j)) "
                + "for every caller tape j. Tuple components in the formula below always "
                + "belong to its quantified x. Let V(w) be the finite lists of natural "
                + "pairs (u,v) satisfying u < 2^w and 0 < v < 2^w at every entry.")),
            Paragraph(Text(
                "For x in X, set A = fixedBits(w,a), B = fixedBits(w,d), "
                + "Q = fixedBits(w,a/d), and R = fixedBits(w+1,a%d). Let "
                + "E = callEntry(A,B,capacity,oldQ,oldR) and "
                + "e(n) = prefixCharge((E,the constant zero map),initialCharge(w),n). "
                + "Write P(x,n) for FramedCall(w,a,d,capacity,oldQ,oldR,caller,frame,"
                + "initialCharge(w),n), and G(x,n,l) for "
                + "RepeatedCalls(w,capacity,caller,frame,A,B,Q,R,e(n),l). "
                + "These are the single-call and recursive call predicates described below.")),
            Paragraph(Text(
                "Let J mean that signedHeadDescription and describeControl are injective "
                + "and that length(codeDescription) + length(describeControl(c)) = "
                + "fixedCodeCharge for every finite-control state c. Write Tdiv(w) for "
                + "divPositiveRunTime(w). In the existential quantifier, D and U range over "
                + "maps from FramedCfg to optional FramedCfg; k, Cstep, Cframe and K are "
                + "natural numbers. Thus the following statement fixes the machine and "
                + "constants before quantifying over all inputs and finite histories.")),
            Describe.Lean(
                DescribeId.Create("framed-physical-divider-histories"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/PhysicalDivider/Histories.framed_divider_histories"),
                H("Uniform calls with persistent physical storage"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("D"), Comma, F.Id("U"), Comma, F.Id("k"), Comma,
                    F.Id("Cstep"), Comma, F.Id("Cframe"), Comma, F.Id("K"), Comma, Sp,
                    F.Id("D"), Eq, F.Id("framedStep"), Sp, Land, Sp,
                    F.Id("U"), Eq, F.Id("framedAgain"), Sp, Land, Sp,
                    F.Id("k"), Eq, Bar, F.Id("FramedTape"), Bar, Sp, Land, Sp,
                    F.Id("k"), Eq, D(1, 6), Sp, Land, Sp,
                    F.Id("Cstep"), Eq, F.Id("sourceStepBudget"), Sp, Land, Sp,
                    F.Id("Cframe"), Eq, D(3, 0, 1), Sp, Land, Sp,
                    F.Id("K"), Eq, F.Id("framedSpaceConstant"), Sp, Land, Sp,
                    D(0), Lt, F.Id("Cstep"), Sp, Land, Sp,
                    D(0), Lt, F.Id("Cframe"), Sp, Land, Sp,
                    D(0), Lt, F.Id("K"), Sp, Land, Sp,
                    Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("X"), Comma, Sp,
                    Exists, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("J"), Sp, Land, Sp, F.Id("P"), Open, F.Id("x"), Comma, F.Id("n"), Close, Sp, Land, Sp,
                    F.Id("n"), Le, Sp, F.Id("Cstep"), Open, F.Id("Tdiv"), Open, F.Id("w"), Close,
                    Plus, D(2), Close, Plus, F.Id("Cframe"), Open, F.Id("w"), Plus, D(1), Close, Sp, Land, Sp,
                    Forall, Sp, F.Id("l"), InMacro, Sp, F.Id("V"), Open, F.Id("w"), Close, Comma, Sp,
                    F.Id("G"), Open, F.Id("x"), Comma, F.Id("n"), Comma, F.Id("l"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The machine, its sixteen-tape family, finite control and positive constants "
                        + "are fixed before the width, operands, caller contents and number of calls. "
                        + "Fourteen tapes hold the divider stacks, operands, capacity, scratch and output. "
                        + "Two additional tapes hold arbitrary protected caller data. Every instruction "
                        + "performs one bit read, one bit write or one unit move on a selected active tape. "
                        + "Administrative transitions and return signalling use counted reads.")),
                    Paragraph(Text(
                        "For width w at least one, the dividend satisfies 0 <= a < 2^w and the divisor "
                        + "satisfies 0 < d < 2^w. The capacity buffer has w bits. Old quotient and "
                        + "remainder buffers have lengths at most w and w+1, respectively. Active heads "
                        + "start at the parked boundary. The machine executes loading, reversal, padding, "
                        + "copying, division, output transfer, scratch clearing and parking. It returns "
                        + "fixedBits(w,a/d) and fixedBits(w+1,a%d), with the operand copies and protected "
                        + "caller tapes preserved. Scratch and obsolete active output have been cleared.")),
                    Paragraph(Text(
                        "The source arithmetic time is Tdiv(w) = 2(w+1)+3+w(6(w+1)+10)+1. "
                        + "Cstep is the fixed sum of the bounded source-statement implementation budgets. "
                        + "The physical arithmetic proof uses the source divider's positive timed "
                        + "correctness theorem and controls stack growth separately within each short "
                        + "round. Preparation and return contribute a linear allowance. The coefficient "
                        + "301 also pays the one-read reentry before a subsequent call.")),
                    Paragraph(Text(
                        "F counts the protected tape intervals and their signed binary head descriptions. "
                        + "The remaining charge includes all active intervals, the encoded transition "
                        + "table, current finite control and signed binary active-head descriptions. "
                        + "Initial intervals include every encoded cell, including zero-valued cells "
                        + "and both bits of every delimiter. Every execution prefix retains all earlier "
                        + "charged intervals and contains earlier support and head positions. Erasure "
                        + "therefore cannot reduce the charged interval. The absolute positive K is "
                        + "independent of every operand and of the number of completed calls.")),
                    Paragraph(Text(
                        "After any return, each next operand is supplied by an explicit sequence of "
                        + "writes and unit moves. A w-bit operand requires 6w+6 such actions. These two "
                        + "production costs are separate from the division time bound. This count "
                        + "covers writing already supplied bits; computing those bits in the "
                        + "surrounding executor has an additional, separate cost. Production "
                        + "preserves every other tape, returns the changed operand's head to the origin "
                        + "and retains all charged endpoints through every prefix. The following "
                        + "reentry read changes only control. Induction over an arbitrary finite list "
                        + "of valid operand pairs connects these exact returned boundaries without "
                        + "resetting the accumulated charge.")),
                    Paragraph(Text(
                        "The result concerns this framed divider. It does not implement a six-codeword "
                        + "parser, a complete ML initializer or executor, an approximation transfer, "
                        + "or a quotient or hardware interpretation."))),
                DescribeRole.Theorem))));
}
