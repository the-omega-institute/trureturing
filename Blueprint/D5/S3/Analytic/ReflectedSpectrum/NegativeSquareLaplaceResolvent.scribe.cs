using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class NegativeSquareLaplaceResolventDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/NegativeSquareLaplaceResolvent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative-square mode has an exact damping threshold and Laplace resolvent.",
        H("Negative-Square Laplace Resolvent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stabilization-gap-definition"),
                DeclarationHandle.Create(Prefix + "stabilizationGap"),
                H("The stabilization gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The gap adds scalar damping to the frozen signed spectral atom. Because the "
                        + "atom is minus delta squared, the resulting denominator is damping "
                        + "minus delta squared."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("damped-kernel-definition"),
                DeclarationHandle.Create(Prefix + "dampedNegativeSquareKernel"),
                H("The damped forward kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward kernel is the real exponential with rate equal to minus the "
                        + "stabilization gap. Its half-line integrability detects the exact "
                        + "damping threshold."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-square-resolvent-definition"),
                DeclarationHandle.Create(Prefix + "negativeSquareResolvent"),
                H("The scalar negative-square resolvent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The scalar resolvent is the inverse stabilization gap. Its pole occurs when "
                        + "the applied damping exactly equals the squared reflected split."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("laplace-resolvent-package"),
                DeclarationHandle.Create(Prefix + "negative_square_laplace_resolvent"),
                H("Threshold, integrability, integral, and pole agree"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Pinned Mathlib improper-integral theorems show that the damped kernel is "
                            + "integrable on the positive half-line exactly when damping exceeds "
                            + "delta squared. Above this threshold, its integral is the inverse "
                            + "gap.")),
                    Paragraph(Text(
                        "The same threshold characterizes positivity of the scalar resolvent, "
                            + "while equality marks its pole. This closes the local stabilization "
                            + "debt and does not construct a global zeta resolvent."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum")),
        ]));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Typed(Formula value) => Seq(value, Colon, Sp, Reals());

    private static Formula PowerTwo(Formula value) => Seq(value, Caret, Grp(D(2)));

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

    private static Formula MainFormula()
    {
        Formula delta = F.Id("delta");
        Formula damping = F.Id("u");
        Formula threshold = Seq(PowerTwo(delta), Sp, Lt, Sp, damping);
        Formula kernel = Call("dampedNegativeSquareKernel", delta, damping);
        Formula resolvent = Call("negativeSquareResolvent", delta, damping);
        Formula gap = Call("stabilizationGap", delta, damping);
        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(delta), Comma, Sp, Typed(damping), Comma, Sp,
                Grp(Seq(Call("IntegrableOnIoi", kernel, D(0)), Sp, Iff, Sp, threshold)),
                Sp, Land),
            Seq(
                Grp(Seq(threshold, Sp, Rightarrow, Sp,
                    Call("IntegralIoi", kernel, D(0)), Sp, Eq, Sp, resolvent)),
                Sp, Land),
            Seq(
                Grp(Seq(D(0), Sp, Lt, Sp, resolvent, Sp, Iff, Sp, threshold)),
                Sp, Land),
            Seq(
                Grp(Seq(gap, Sp, Eq, Sp, D(0), Sp, Iff, Sp,
                    damping, Sp, Eq, Sp, PowerTwo(delta))), Dot),
        ]));
    }
}
