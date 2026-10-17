using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.BurnolGram;

internal sealed class SameWindowLogarithmicErrorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/BurnolGram/SameWindowLogarithmicError.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual same-window smooth error belongs to the logarithmically weighted Fourier space and converges to zero there with an explicit boundary-width rate.",
        H("Logarithmic Fourier convergence in the same window"),
        Blocks(
            Paragraph(Text(
                "Let p be any even infinitely differentiable complex function. Write T_h=chi_h*p "
                + "for the actual interior-box smooth test, and E_h=1_{(-a,a)}p-T_h for its "
                + "zero-extension error. The error may jump at the original endpoints; its "
                + "Fourier transform is the ordinary scalar integral with angular kernel exp(-i*t*x).")),
            Describe.Lean(
                DescribeId.Create("same-window-error-angular-transform"),
                DeclarationHandle.Create(Owner + "sameWindowErrorFourier"),
                H("The angular transform of the actual error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive width h, define F_h(t) as the integral over the real line of "
                    + "exp(-i*t*x)*E_h(x). The input is the actual zero-extension error and is "
                    + "not asserted to be a smooth compactly supported Weil test."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("same-window-logarithmic-error-norm"),
                DeclarationHandle.Create(Owner + "sameWindowLogarithmicError"),
                H("The logarithmically weighted angular norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For h>0 let Q_h=(1/(2*pi))*integral (1+log(1+|t|))*|F_h(t)|^2 dt. "
                    + "The scalar factor corresponds to angular frequency. Set Q_h=0 for "
                    + "nonpositive h to obtain a function on the entire width line; these "
                    + "values do not affect its limit from positive widths."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("same-window-logarithmic-error-rate"),
                DeclarationHandle.Create(Owner + "sameWindowSmoothTrial_logarithmic_error_le"),
                H("Weighted integrability and an explicit error rate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume h>0, 4h<=a, M,M1>=0, and |p|<=M, |p'|<=M1 on [-a,a]. "
                    + "The actual weighted function (1+log(1+|t|))*|F_h(t)|^2 is integrable, "
                    + "and 0<=Q_h<=(h/pi)*(16M^2+(4M+a*M1)^2)*(2+log(1+1/h)). "
                    + "Dominated continuity follows from integrability of E_h. A finite central "
                    + "frequency interval and two reflected logarithmic tails provide an "
                    + "actual integrable majorant. Weighted integrability is established "
                    + "before integration of this domination. The actual endpoint-decay "
                    + "bound supplies the high-frequency estimate, and the split at 1/h "
                    + "gives the stated constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-window-logarithmic-error-right-limit"),
                DeclarationHandle.Create(Owner + "tendsto_sameWindowSmoothTrial_logarithmic_error"),
                H("Convergence for every fixed smooth even input"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a>0, a smooth even p, and nonnegative bounds M,M1 for p and p' "
                    + "on [-a,a]. Then Q_h tends to zero as h tends to zero through positive "
                    + "values. Eventually 4h<=a, so the proved error rate applies to the "
                    + "entire positive-width family. The scalar rate tends to zero because "
                    + "h*(2+log(1+1/h))=2h+h*log(1+h)-h*log h. The logarithmic Fourier "
                    + "estimate alone does not identify the closed Gamma, pole and prime "
                    + "Weil form or supply a signed negative trial."))),
                DescribeRole.Theorem))));
}
