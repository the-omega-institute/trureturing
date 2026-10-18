using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class PeriodicEnergyComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "AE evenness of the original zero extension orders the full extended actual Gamma translation energies.",
        H("Extended actual Gamma periodic energy comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-gamma-periodic-energy-order"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaGamma/PeriodicEnergyComparison."
                    + "actual_gamma_order_of_zero_extension_ae_even"),
                H("Periodic energy is bounded by zero-extension energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d>0 and t be arbitrary real numbers, I=(t,t+d], and u:R->C "
                        + "satisfy MemLp(u,2,Lebesgue restricted to I). Let z=1_I*u be the "
                        + "original indicator zero extension, and v(x)=AddCircle.liftIoc(d,t,u)"
                        + "(x mod d). Assume only z(-x)=z(x) for Lebesgue-almost-every x "
                        + "on the whole real line. No pointwise parity, endpoint trace, real-valuedness, "
                        + "smoothness or full-Gamma-energy finiteness is assumed.")),
                    Paragraph(Text(
                        "Use the existing ArchimedeanJumpDecomposition.archimedeanJumpDensity, "
                        + "rho(s)=exp(-s/2)/(1-exp(-2*s)) for s>0. Put Ep(s)=integral_I "
                        + "|u(x)-v(x-s)|^2 dx and E0(s)=integral_R |z(x)-z(x-s)|^2 dx. "
                        + "The exact conclusion is integral_{s>0} ofReal(rho(s))*ofReal(Ep(s)) ds "
                        + "<= integral_{s>0} ofReal(rho(s))*ofReal(E0(s)) ds. Both outer integrals "
                        + "live in ENNReal and either may be infinite; no infinite total is converted "
                        + "to a real number or subtracted. The symmetric original window is "
                        + "the specialization d=2*a, t=-a, a>0, with the same indicator and actual liftIoc.")),
                    Paragraph(Text(
                        "For each b>0 use w_b(s)=exp(-b*|s|). Absolute lattice unfolding and "
                        + "the physical L2 correlation expansions prove the finite single-rate identity "
                        + "E0_b=Ep_b+Re B_b, with coefficient ONE for the noncentral Hermitian image "
                        + "pairing. On -d<=x-y<=d its image kernel is 2*cosh(b*(x-y))/(exp(b*d)-1). "
                        + "For M_b=integral_I exp(b*x)*u(x) dx, the exact correction is "
                        + "B_b=conjugate(M_{-b})*M_b/(exp(b*d)-1)"
                        + "+conjugate(M_b)*M_{-b}/(exp(b*d)-1). Both denominators are exp(b*d)-1; "
                        + "complex conjugates are retained before taking the real part.")),
                    Paragraph(Text(
                        "Global AE evenness of the original zero extension gives M_{-b}=M_b "
                        + "by full-line reflection, so Re B_b=2*|M_b|^2/(exp(b*d)-1)>=0. "
                        + "The existing density-series proof, reused from its original owner, "
                        + "expands rho(s) as sum_{r>=0} exp(-(2*r+1/2)*s) for s>0. Each finite-rate "
                        + "energy is integrable because the corresponding translation energy lies "
                        + "between zero and four times the physical L2 mass. Nonnegative Tonelli "
                        + "then expresses each extended Gamma energy as the ENNReal sum of its "
                        + "finite-rate energies and sums their inequalities. No summability of "
                        + "the crude mass-over-rate bounds is assumed.")),
                    Paragraph(Text(
                        "This proves the nonnegative actual-Gamma translation-energy comparison. "
                        + "It establishes no positivity of the full signed Weil form, Schur complement "
                        + "or Robin realization, and it does not prove RH. Literature novelty is not asserted."))),
                DescribeRole.Theorem))));
}
