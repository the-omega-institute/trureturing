using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class GoldenShellMomentBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden shell membership bounds every nonnegative transverse defect moment between the shell transcript and its one-step rescaling.",
        H("Golden Shell Moment Bounds"),
        Blocks(
            Theorem("golden-shell-moment-bounds", "golden_shell_moment_bounds",
                "Golden Shells Bound Transverse Moments", GoldenShellMomentBoundsFormula(),
                "Assign each nonnegative defect multiplicity to the unique golden shell whose adjacent scales enclose that defect. For every nonnegative real exponent, the actual defect moment lies below the shell transcript moment and above its one-shell golden rescaling.",
                "Extended nonnegative real sums retain the statement for infinite index families without adding a convergence hypothesis; the shell membership inequalities are the only external assumptions."),
            Theorem("golden-shell-moment-valid-witness", "golden_shell_moment_valid_witness",
                "A Shell-Zero Singleton Attains One Quarter", ValidWitnessFormula(),
                "A singleton of multiplicity one at defect one half lies in shell zero. At exponent two, both the transcript moment and the actual defect moment evaluate to one quarter.",
                "This explicit calculation witnesses that the hypotheses and conclusion are simultaneously inhabited."),
            Theorem("golden-shell-moment-outside-shell-witness",
                "golden_shell_moment_outside_shell_witness",
                "An Outside-Shell Singleton Breaks the Upper Bound", OutsideWitnessFormula(),
                "A singleton assigned to shell zero but placed at defect two violates the shell upper endpoint. At exponent one, its actual moment is two while its transcript moment is one half.",
                "The numerical separation shows that the shell membership premise carries mathematical content."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula GoldenShellMomentBoundsFormula()
    {
        Formula s = F.Id("s");
        Formula transcript = Call("G", s);
        Formula defectMoment = Call("zetaPerp", s);
        Formula lower = Seq(Pow(Call("goldenShellStep"), s), Sp, Times, Sp,
            transcript, Sp, Le, Sp, defectMoment);
        Formula upper = Seq(defectMoment, Sp, Le, Sp, transcript);
        return Disp(Seq(Open, lower, Close, Sp, Land, Sp, Open, upper, Close, Dot));
    }

    private static Formula ValidWitnessFormula()
    {
        Formula quarter = Fraction(D(1), D(4));
        return Disp(Seq(Call("G", D(2)), Sp, Eq, Sp, quarter, Sp, Land, Sp,
            Call("zetaPerp", D(2)), Sp, Eq, Sp, quarter, Dot));
    }

    private static Formula OutsideWitnessFormula()
    {
        return Disp(Seq(Call("G", D(1)), Sp, Eq, Sp, Fraction(D(1), D(2)), Comma, Sp,
            Call("zetaPerp", D(1)), Sp, Eq, Sp, D(2), Comma, Sp,
            Call("zetaPerp", D(1)), Sp, Gt, Sp, Call("G", D(1)), Dot));
    }

    private static Formula Pow(Formula basis, Formula exponent) =>
        Seq(Grp(basis), Caret, Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
}
