using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class ApproximateComplementaryConcentrationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residual spectral energy controls the mass away from Fourier near-zeros.",
        H("Approximate Complementary Concentration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("approximate-complementary-concentration"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/ApproximateComplementaryConcentration."
                        + "approximate_complementary_concentration"),
                H("Residual spectral mass concentrates near Fourier zeros"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a positive Borel measure carry the residual spectrum and let a "
                            + "measurable complex function be the Fourier transform of the "
                            + "window test.")),
                    Paragraph(Text(
                        "If its squared modulus has residual energy epsilon, Markov's "
                            + "inequality bounds the mass where the modulus exceeds a positive "
                            + "finite threshold delta by epsilon divided by delta squared."))),
                DescribeRole.Theorem))));

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

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula ennreal = Call("ENNReal");
        Formula residual = F.Id("mu");
        Formula fourier = F.Id("F");
        Formula epsilon = F.Id("epsilon");
        Formula delta = F.Id("delta");
        Formula deltaENNReal = Call("toENNReal", delta);
        Formula xi = F.Id("xi");
        Formula fourierAtXi = Call("enorm", Call("apply", fourier, xi));
        Formula squaredModulus = new Formula.Power(fourierAtXi, D(2));
        Formula squaredDelta = new Formula.Power(deltaENNReal, D(2));
        Formula thresholdSet = new Formula.SetBuilder(
            Seq(deltaENNReal, Sp, Leq, Sp, fourierAtXi), xi, real);
        Formula energy = Call(
            "lintegral", residual,
            Lambda(Seq(xi, Colon, Sp, real), squaredModulus));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp,
                residual, Colon, Sp, Call("Measure", real), Comma, Sp,
                fourier, Colon, Sp, real, Sp, To, Sp, complex, Comma),
            Seq(epsilon, Colon, Sp, ennreal, Comma, Sp,
                delta, Colon, Sp, F.Id("NNReal"), Comma),
            Seq(Call("AEMeasurable", fourier, residual), Sp, Land, Sp,
                D(0), Sp, Lt, Sp, delta, Sp, Land, Sp,
                energy, Sp, Eq, Sp, epsilon, Sp, Rightarrow),
            Seq(Call("measure", residual, thresholdSet), Sp, Leq, Sp,
                Frac, Grp(epsilon), Grp(squaredDelta), Dot),
        ]));
    }
}
