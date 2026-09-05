using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class TerminalShellParityLawDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Deficit/TerminalShellParityLaw.terminal_shell_defect_iff_odd";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under the terminal first-sign law, defect status is exactly odd shell parity.",
        H("Terminal Shell Parity Law"),
        Blocks(Describe.Lean(
            DescribeId.Create("terminal-shell-defect-iff-odd"),
            DeclarationHandle.Create(Declaration),
            H("Terminal defect is equivalent to odd shell parity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The integer terminalSign represents the sign of the source tail term. "
                        + "The premise records the first-sign law exactly: terminalSign equals "
                        + "(-1) raised to K-1+a. Defect is the equality with (-1)^a.")),
                Paragraph(Text(
                    "The positive-shell hypothesis is essential. Lean natural subtraction "
                        + "truncates at zero, and at K=0 the displayed sign equality holds even "
                        + "though Odd(K) is false. Writing 0<K removes that false branch.")),
                Paragraph(Text(
                    "After expressing K as a successor, Mathlib's even and odd negative-one "
                        + "power laws reduce the statement to successor parity. The same module "
                        + "also proves that the opposite terminal sign occurs exactly for even "
                        + "K. Numerical root scans, window errors, and the open middle region "
                        + "are not asserted."))),
            DescribeRole.Theorem))));

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula shell = F.Id("K");
        Formula row = F.Id("a");
        Formula sign = F.Id("terminalSign");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula minusOne = Grp(Minus, D(1));
        Formula firstExponent = Seq(shell, Sp, Minus, Sp, D(1), Sp, Plus, Sp, row);
        Formula firstSign = Power(minusOne, firstExponent);
        Formula defectSign = Power(minusOne, row);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, shell, Comma, Sp, row, InMacro, Sp, naturals, Comma, Sp,
                sign, InMacro, Sp, integers, Comma),
            Seq(
                D(0), Sp, Lt, Sp, shell, Sp, Land, Sp,
                sign, Sp, Eq, Sp, firstSign, Sp, Rightarrow),
            Seq(
                sign, Sp, Eq, Sp, defectSign, Sp, Iff, Sp,
                Call("Odd", shell), Dot),
        ]));
    }
}
