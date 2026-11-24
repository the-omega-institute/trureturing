using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MangoldtFejerActualOrdinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fejér averages tested at the positive zeta ordinates",
        H("The limit of the largest admissible coefficient"),
        Blocks(
            Paragraph(Text(
                "At scale T, a probability measure μ on the interval from zero to one half is "
                + "admissible if its cosine transform is nonnegative at γ/T for every positive "
                + "ordinate γ of a nontrivial zeta zero. Its coefficient A is half the μ-average "
                + "of b/2 − b².")),
            Describe.Lean(
                DescribeId.Create("eventually-fejer-averaging-coefficient-le"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerActualOrdinates.eventually_fejer_averaging_coefficient_le"),
                H("The bound on a common tail"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(F.Id("A"),
                    FormulaRelationOperator.LessThanOrEqual, Add(Coefficient(), F.Id("epsilon"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each positive ε the scale threshold is uniform over the admissible measures. "
                    + "The unconditional cumulative Riemann–von Mangoldt law puts a scaled ordinate "
                    + "arbitrarily near each fixed positive harmonic. Every cosine transform here has "
                    + "Lipschitz constant at most one half. Use the nearby ordinates for a finite set "
                    + "of harmonics and the summable reciprocal-square bound for the remaining terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tendsto-fejer-coefficient-supremum"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerActualOrdinates.tendsto_sSup_fejerAveragingCoefficients"),
                H("The exact limit"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Seq(Lim, Underscore, Grp(F.Id("T"), To, Infty), Sp,
                        new Formula.FunctionCall(FormulaIdentifier.Create("supremum"), [F.Id("T")])),
                    FormulaRelationOperator.Equal, Coefficient()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here supremum(T) ranges over the coefficients of all measures admissible at scale T. "
                    + "The triangular law is admissible at every scale and gives 1/48. The common upper "
                    + "bound proves convergence to that value."))),
                DescribeRole.Theorem))));

    private static Formula Coefficient() => new Formula.Fraction(D(1), D(4, 8));
}
