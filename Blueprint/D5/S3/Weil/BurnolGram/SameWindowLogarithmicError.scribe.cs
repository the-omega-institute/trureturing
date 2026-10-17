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
                DescribeRole.Theorem),
            Paragraph(Text(
                "Fix a>0, smooth even p, and M,M1>=0 with |p|<=M and |p'|<=M1 on [-a,a]. "
                + "Let f=1_{(-a,a)}p, U(t)=integral exp(-i*t*x)*f(x) dx, and, for h>0, "
                + "V_h(t)=integral exp(-i*t*x)*T_h(x) dx, with T_h the actual "
                + "sameWindowSmoothTrial. Set V_h=0 for h<=0 only to make the indexed "
                + "family total. Write W(t)=1+log(1+|t|) and F_h(t) for the actual "
                + "sameWindowErrorFourier. All these transforms use the angular kernel; "
                + "the error energy and Gamma quadratic integral both carry 1/(2*pi).")),
            Paragraph(Text(
                "The target f is integrable because p is continuous on the compact "
                + "original window, and every T_h is integrable as a Weil test. For every "
                + "real t, the angular kernel is continuous and has norm one. Its products "
                + "with f and T_h are therefore separately integrable. Expanding the "
                + "integrand and applying integral_sub with these two actual premises "
                + "gives F_h(t)=U(t)-V_h(t). Domination by the respective L1 norm also "
                + "proves continuity of U and of every positive-width V_h; no continuity "
                + "of the zero extension at its endpoints is required.")),
            Paragraph(Text(
                "For each actual smooth trial, the existing closed-strip Fourier bound "
                + "at strip width zero gives |V_h(t)|<=C_h/(1+t^2). The elementary "
                + "inequality 0<=W(t)<=2*(1+t^2) then bounds W(t)*|V_h(t)|^2 by "
                + "2*C_h^2/(1+t^2), an integrable function. To obtain membership of the "
                + "target itself, choose the one fixed width h0=a/8. It is positive and "
                + "satisfies 4*h0<=a. The weighted error theorem supplies integrability "
                + "of W*|F_h0|^2. The exact identity U=V_h0+F_h0 and "
                + "|z+w|^2<=2*(|z|^2+|w|^2) supply an integrable majorant for W*|U|^2. "
                + "Thus target membership is proved from the actual approximation, "
                + "rather than imposed as a further hypothesis.")),
            Paragraph(Text(
                "As h tends to zero through positive values, eventually h<a/4 and "
                + "hence 4h<=a. At those widths the proved weighted theorem supplies "
                + "integrability of W*|F_h|^2, and its normalized integral tends to zero. "
                + "Since normSq(V_h-U)=|F_h|^2, this is exactly the error premise of "
                + "actual_gamma_quadratic_tendsto_of_log_weight_error, with index type "
                + "the real line and filter nhdsWithin 0 (Ioi 0). Its other premises "
                + "are the frequency continuity and target membership established above. "
                + "Consequently (1/(2*pi))*integral (2*pi*Zeta23.mu(t))*normSq(V_h(t)) dt "
                + "tends to (1/(2*pi))*integral (2*pi*Zeta23.mu(t))*normSq(U(t)) dt.")),
            Paragraph(Text(
                "This application concerns the actual Gamma density and the raw "
                + "transform of the original zero extension, for every fixed smooth "
                + "even p and positive radius a. Each T_h may use the already established "
                + "smooth archimedean identity directly. The application does not require "
                + "a raw/L2 Fourier identification and does not assert a closed Gamma "
                + "form or domain, convergence of the full pole and prime terms, "
                + "a signed negative trial, or the Riemann hypothesis."))
        )));
}
