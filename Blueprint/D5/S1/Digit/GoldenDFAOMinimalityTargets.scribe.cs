using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenDFAOMinimalityTargetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "M07-M16 register exact finite-prefix LRAT targets for the "
            + "golden-ratio DFAO controls and the base-4 state-exclusion "
            + "ladder.",
        H("Golden-Ratio DFAO Minimality Targets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("base4-problem-semantics"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/GoldenDFAOMinimalityTargets.base4_problem_semantics"),
                H("The registered problem uses the exact frozen oracle"),
                StatementSource.FromAuthor(SemanticsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The registered sparse input at index i is definitionally the canonical most-significant-digit-first Zeckendorf word of four to the i, and the registered target output equals the exact golden-ratio floor difference certified by the frozen base-4 oracle layer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("base4-twenty-two-state-minimality-interface"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/GoldenDFAOMinimalityTargets.phi_base4_twenty_two_state_minimality"),
                H("A verified upper machine and the M16 refutation imply exact minimality"),
                StatementSource.FromAuthor(TerminalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The terminal theorem consumes two independent evidence objects: a globally correct twenty-two-state typed machine and a certified finite-prefix LRAT refutation of every machine using at most twenty-one states.")),
                    Paragraph(Text(
                        "The theorem is a certificate eliminator. It does not assert that either external evidence object has already been constructed or checked."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula FourPow(Formula exponent) =>
        Seq(D(4), Caret, Grp(exponent));

    private static Formula FloorPhiTimes(Formula power) => Seq(
        Lfloor, power, Cdot, Varphi, Rfloor);

    private static Formula SemanticsFormula() => Disp(Seq(
        Call("input", F.Id("P"), F.Id("i")),
        Sp, Eq, Sp,
        Call("W", FourPow(F.Id("i"))),
        Sp, Land, Sp,
        Call("target", F.Id("P"), F.Id("i")),
        Sp, Eq, Sp,
        FloorPhiTimes(FourPow(Seq(F.Id("i"), Plus, D(1)))),
        Minus, D(4), Cdot,
        FloorPhiTimes(FourPow(F.Id("i")))));

    private static Formula TerminalFormula() => Disp(Seq(
        Call("HasGlobalModel", F.Id("P"), D(2, 2)),
        Sp, Land, Sp,
        Call("Refutation", Call("formula", F.Id("E"))),
        Sp, Implies, Sp,
        Call("IsMinimalStateCount", F.Id("P"), D(2, 2))));
}
