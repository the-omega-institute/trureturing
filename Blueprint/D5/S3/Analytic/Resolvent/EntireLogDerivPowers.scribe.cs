using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Resolvent;

internal sealed class EntireLogDerivPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute zero power sums encode every positive logarithmic derivative order.",
        H("Zero Power Sums of Entire Functions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("entire-log-deriv-power-has-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Resolvent/EntireLogDerivPowers.entire_logDeriv_power_hasSum"),
                H("The multiplicity weighted inverse power identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be complex differentiable everywhere and let alpha and C be real. "
                        + "Assume alpha<2 and norm(F(z))<=exp(C*(1+norm(z))^alpha) for every z. "
                        + "For every integer k>=1 and every complex a with F(a) nonzero, "
                        + "the family "
                        + "m(rho)*inverse(a-rho)^(k+1) has sum "
                        + "((-1)^k/k!)*iteratedDeriv(k,logDeriv(F),a). Here the index is the "
                        + "subtype of all zeros, m(rho)=analyticOrderNatAt(F,rho), and the "
                        + "family is absolutely summable. Zero repetitions are represented "
                        + "by this actual analytic multiplicity.")),
                    Paragraph(Text(
                        "The known inverse square summability with denominator "
                        + "1+norm(rho-a)^2 becomes inverse distance square summability because "
                        + "continuity gives a zero free ball about a. Choose delta>0 so that "
                        + "norm(a-rho)>=2*delta for every zero rho. If norm(y-a)<delta, "
                        + "then norm(inverse(y-rho))<=2*norm(inverse(a-rho)) and "
                        + "norm(inverse(y-rho))<=inverse(delta). Hence the inverse power "
                        + "of order n+2 is bounded by "
                        + "4*inverse(delta)^n*norm(inverse(a-rho))^2, uniformly in this ball. "
                        + "The multiplicity weighted majorant is summable.")),
                    Paragraph(Text(
                        "Apply termwise differentiation first to the convergent two point "
                        + "logarithmic derivative difference. Its derivative is the negative "
                        + "inverse square zero sum. The same local majorant applies to every "
                        + "higher inverse power. Induction differentiates the sum and yields "
                        + "the exact sign and factorial. The entire function growth hypothesis "
                        + "enters through the existing two point identity and zero summability, "
                        + "while the uniform local inverse power estimate justifies the new "
                        + "differentiation step. Hadamard factorization and the resulting two "
                        + "point logarithmic derivative identity are classical analytic inputs, "
                        + "formalized in EntireLogDerivDifference. This module supplies the "
                        + "local uniform domination, termwise differentiation, and positive "
                        + "order induction in Lean.")),
                    Paragraph(Text(
                        "Order zero is excluded because a constant term in the logarithmic "
                        + "derivative is not recovered by differentiating the two point formula. "
                        + "The nonzero center condition permits an arbitrary local zero free ball; "
                        + "no global restriction on the zero locations is imposed. "
                        + "No character, arithmetic coefficient, conductor bound, or estimate "
                        + "for an individual Dirichlet L function is asserted by this identity. "
                        + "Such applications must separately identify the entire function and "
                        + "its logarithmic derivatives."))),
                DescribeRole.Theorem))));
}
