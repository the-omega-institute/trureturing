using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class LogarithmicRadialDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic Cayley radius detects the midline and reverses under the mirror.",
        H("Logarithmic Radial Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("logarithmic-radial-defect-and-mirror"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/Cayley/LogarithmicRadialDefect."
                        + "logarithmic_radial_defect_and_mirror"),
                H("Logarithmic radial defect and mirror reversal"),
                StatementSource.FromAuthor(DefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Z be the canonical exhaustive, duplicate-free source-zero carrier. "
                            + "For a complex point rho, c(rho) is the imported Cayley coefficient "
                            + "(rho - 1)/rho, and beta(rho) is log |c(rho)|.")),
                    Paragraph(Text(
                        "The first public conjunct rewrites beta on every indexed source zero as "
                            + "one half the logarithm of the squared-norm ratio. The second applies "
                            + "the canonical Cayley unitarity criterion to identify simultaneous "
                            + "vanishing with the global midline predicate.")),
                    Paragraph(Text(
                        "The remaining public conjuncts state reciprocal Cayley norm and logarithmic "
                            + "sign reversal under the imported conjugate-reflection mirror. The "
                            + "open-strip fields stored in ZeroData exclude both zero and one, so "
                            + "the coefficient norm used in the midline argument is positive.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the logarithm-of-a-square and logarithm-of-an-inverse "
                            + "identities. The mirror norm calculation uses the canonical complex "
                            + "conjugation norm identity rather than introducing a second reflection."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Norm(Formula value) =>
        Seq(Vert, Sp, value, Vert);

    private static Formula Square(Formula value) =>
        Seq(value, Caret, Grp(D(2)));

    private static Formula DefectFormula()
    {
        Formula data = F.Id("Z");
        Formula index = F.Id("n");
        Formula rho = Seq(Rho, Underscore, Grp(index));
        Formula coefficient = Apply(F.Id("c"), rho);
        Formula mirrorRho = Apply(Seq(Operatorname, Grp(F.Id("mirror"))), rho);
        Formula mirroredCoefficient = Apply(F.Id("c"), mirrorRho);
        Formula beta = Apply(Beta, rho);
        Formula mirroredBeta = Apply(Beta, mirrorRho);
        Formula squaredRatio = Seq(
            Frac,
            Grp(Square(Norm(Seq(rho, Minus, D(1))))),
            Grp(Square(Norm(rho))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, data, Colon, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            beta, Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(2)), Sp, Log, Sp, Open, squaredRatio, Close,
            Close, Sp, Land, RowBreak, Grp(),
            Open, Operatorname, Grp(F.Id("AllZerosOnMidline")), Open, data, Close,
            Sp, Leftrightarrow, Sp, Forall, Sp, index, Comma, Sp,
            beta, Sp, Eq, Sp, D(0), Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            Norm(mirroredCoefficient), Sp, Eq, Sp,
            Norm(coefficient), Caret, Grp(Minus, D(1)), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            mirroredBeta, Sp, Eq, Sp, Minus, beta, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
