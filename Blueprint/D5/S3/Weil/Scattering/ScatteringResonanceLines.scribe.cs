using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class ScatteringResonanceLinesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zeta critical line becomes the resonance quarter line and its reflected "
        + "antiresonance three-quarter line.",
        H("Scattering Resonance Lines"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scattering-resonance-lines"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Scattering/ScatteringResonanceLines."
                        + "scattering_resonance_lines"),
                H("Critical zeros map to the two scattering lines"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The declaration uses the canonical critical-strip zeta-zero predicate. "
                            + "Dividing a zero parameter by two divides its real part by two, so "
                            + "the critical half-line is equivalent to the resonance quarter line.")),
                    Paragraph(Text(
                        "Reflecting that parameter through one sends real part one quarter to "
                            + "real part three quarters, yielding the independent antiresonance "
                            + "equivalence in the second public conjunct."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula rho = F.Id("rho");
        Formula critical = ZeroLine(rho, rho, new Formula.Fraction(D(1), D(2)));
        Formula resonance = ZeroLine(
            rho,
            new Formula.Fraction(rho, D(2)),
            new Formula.Fraction(D(1), D(4)));
        Formula antiresonance = ZeroLine(
            rho,
            Subtract(D(1), new Formula.Fraction(rho, D(2))),
            new Formula.Fraction(D(3), D(4)));
        return Disp(new Formula.Logic(
            new Formula.Logic(critical, FormulaLogicOperator.Iff, resonance),
            FormulaLogicOperator.And,
            new Formula.Logic(critical, FormulaLogicOperator.Iff, antiresonance)));
    }

    private static Formula ZeroLine(Formula rho, Formula parameter, Formula line) => Seq(
        Left, Open,
        Forall, Sp, rho, Sp, InMacro, Sp, Complexes(), Comma, Esc,
        Call("IsNontrivialZero", rho), Sp, Rightarrow, Sp,
        RealPart(parameter), Sp, Eq, Sp, line,
        Right, Close);

    private static Formula RealPart(Formula argument) => Seq(Re, Open, argument, Close);

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }
            pieces.Add(arguments[index]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
