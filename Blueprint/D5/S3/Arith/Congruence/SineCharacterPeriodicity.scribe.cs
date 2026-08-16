using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class SineCharacterPeriodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sine at integer half-turns is the quadratic character modulo four.",
        H("Sine and the Character Modulo Four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-half-turn-sine-is-chi-four"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/SineCharacterPeriodicity."
                    + "sin_pi_mul_nat_div_two_eq_chi_four"),
                H("Integer half-turn sine equals the character modulo four"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Sin, Open, Frac, Grp(Pi, Sp, F.Id("n")), Grp(D(2)), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("chi")), Underscore, Grp(D(4)), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural number n, sine at pi n divided by two equals the real cast "
                        + "of the quadratic character modulo four. Thus the values on residue classes "
                        + "0, 1, 2, and 3 are respectively 0, 1, 0, and -1.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. It has no exact theorem assembling "
                        + "this sine-character equality, but Real.sin_add_nat_mul_two_pi supplies the "
                        + "period reduction, Real.sin_pi_div_two and Real.sin_add_pi evaluate the odd "
                        + "residues, and ZMod.chi-four-nat-mod-four supplies character periodicity. The "
                        + "Lean proof composes those declarations after quotient-remainder reduction.")),
                    Paragraph(Text(
                        "This closes only the explicit sine-pattern bridge in residual remark 27.9. It "
                        + "does not formalize the Gauss-Jacobi two-squares formula, the associated "
                        + "Dirichlet-series factorization, or the evaluation of the L-series at one."))),
                DescribeRole.Theorem))));
}
