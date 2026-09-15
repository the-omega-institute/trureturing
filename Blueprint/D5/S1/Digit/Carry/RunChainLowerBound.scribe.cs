using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry;

internal sealed class RunChainLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A run of consecutive indices admits a carry chain of quadratic length.",
        H("Carry Chains from a Run of Consecutive Indices"),
        Blocks(
            Paragraph(Text(
                "Raw digits are finitely supported functions from natural numbers to natural "
                + "numbers, added pointwise, and single(i, 1) carries one token at index i. "
                + "A carry step is one of the four replacements of the frozen carry relation, "
                + "and CarrySteps(k, r, t) is a chain of exactly k such steps from r to t. "
                + "The sum below carries one token at each of the L consecutive indices from "
                + "a to a + L - 1, and is the zero digit vector when L is zero. Division is "
                + "natural-number division, so L * L / 4 is the integer part of L squared "
                + "over four.")),
            Describe.Lean(
                DescribeId.Create("run-chain-consecutive-run-chain-length"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Carry/RunChainLowerBound.exists_carrySteps_consecutive_run"),
                H("A chain of quadratic length exists"),
                StatementSource.FromAuthor(ChainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every starting index a and every length L there is a digit vector "
                    + "reached from the run of length L by a chain of exactly L * L / 4 "
                    + "carry steps. The chain is constructed rather than merely shown to "
                    + "exist: one merge at the bottom of the run followed by one split for "
                    + "each remaining duplicate carries the run of length L to the run of "
                    + "length L - 2 together with one isolated token, in L - 1 steps, and a "
                    + "strong induction in steps of two composes these blocks. A parity "
                    + "split evaluates the resulting count under natural-number division. "
                    + "This is a lower bound on the attainable chain length; whether "
                    + "L * L / 4 is also the maximum is not proved here."))),
                DescribeRole.Theorem))));

    private static Formula ChainFormula() => Disp(Universal("a", Naturals(),
        Universal("L", Naturals(),
            Seq(Exists, Sp, F.Id("t"), Sp, InMacro, Sp, F.Id("RawDigits"), Comma, Sp,
                Call3("CarrySteps",
                    Div(Mul(F.Id("L"), F.Id("L")), D(4)),
                    Call2("sum", Call1("range", F.Id("L")),
                        Lambda(F.Id("k"), Call2("single", Add(F.Id("a"), F.Id("k")), D(1)))),
                    F.Id("t"))))));

    private static Formula Naturals() => F.Id("Nat");

    private static Formula Call1(string name, Formula first) =>
        Seq(F.Id(name), Left, Open, first, Right, Close);

    private static Formula Call2(string name, Formula first, Formula second) =>
        Seq(F.Id(name), Left, Open, first, Comma, Sp, second, Right, Close);

    private static Formula Call3(string name, Formula first, Formula second, Formula third) =>
        Seq(F.Id(name), Left, Open, first, Comma, Sp, second, Comma, Sp, third, Right, Close);

    private static Formula Lambda(Formula variable, Formula body) =>
        Seq(F.LambdaLower, Sp, variable, Sp, Mapsto, Sp, body);

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(variable), Sp, InMacro, Sp, domain, Comma, Sp, body);

    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);

    private static Formula Mul(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);

    private static Formula Div(Formula left, Formula right) => Seq(left, Sp, Slash, Sp, right);
}
