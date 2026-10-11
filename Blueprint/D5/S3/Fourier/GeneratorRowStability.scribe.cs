using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class GeneratorRowStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete generator cycle controls phase after translation, and equal spectral amplitudes convert this to a source-energy counting bound.",
        H("Generator Row Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-cycle-phase-correction"),
                DeclarationHandle.Create("D5/S3/Fourier/GeneratorRowStability.complete_cycle_phase_correction"),
                H("Complete cyclic correction from real defect lifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive cyclic order N, let z:ZMod N->Complex have unit norm "
                        + "and z(0)=1. Supply real lifts theta with theta(0)=0 and "
                        + "exp(i theta(k))=z(k)z(1)conj(z(k+1)) for every k, including the final "
                        + "wraparound row. If |theta(k)|<=omega and omega>=0, one actual t:ZMod N "
                        + "satisfies |z(k)-stdAddChar(-(k*t))|<=(N-1)omega/2 at every frequency. "
                        + "The lifts need not be principal and no bound on N*omega is imposed.")),
                    Paragraph(Text(
                        "Write S=sum_{j=0}^{N-1}theta(j). The full recurrence, evaluated also at N, "
                        + "gives z(k)=z(1)^k exp(-i sum_{j<k}theta(j)) and the root "
                        + "q=z(1)exp(-iS/N) with q^N=1. After centering, the phase is "
                        + "Phi(k)=kS/N-sum_{j<k}theta(j). The zero lift improves the prefix bound "
                        + "to (k-1)omega, so |Phi(k)|<=((N-k)(2k-1)/N)omega. The discrete identity "
                        + "N(N-1)-2(N-k)(2k-1)=(2k-N)(2k-N-1)>=0 proves the desired coefficient; "
                        + "it uses that the two factors are consecutive integers. The global "
                        + "chord<=angle estimate then applies even when accumulated phase is large.")),
                    Paragraph(Text(
                        "Mathlib AddChar.zmodChar and FinitePoisson.characterEquiv turn q into a "
                        + "cyclic character. Taking the negative inverse character coordinate gives "
                        + "exactly stdAddChar(-(k*t)), with the translation sign used below. The "
                        + "order-one case has zero bound and remains in the theorem telescope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-amplitude-source-energy"),
                DeclarationHandle.Create("D5/S3/Fourier/GeneratorRowStability.equal_amplitude_signal_energy_stability"),
                H("Equal-amplitude counting stability with exact source energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f,g be arbitrary complex signals on ZMod N, with the unnormalized "
                        + "negative-exponent spectra F=dft(f), J=dft(g). Assume m>0, "
                        + "0<=epsilon<=m^3/4, exact complex DC F(0)=J(0), |F(k)|>=m and "
                        + "|J(k)|=|F(k)| at every k. The complete generator-row residual "
                        + "|J(k)J(1)conj(J(k+1))-F(k)F(1)conj(F(k+1))| is at most epsilon "
                        + "for every k, with cyclic addition and wraparound. Define "
                        + "E_F=(1/N)sum_{k!=0}|F(k)|^2 from the actual source. The theorem produces "
                        + "one t with sum_x|g(x)-f(x-t)|^2<=16(N-1)^2 epsilon^2 E_F/(63m^6). "
                        + "No all-pairs row, zero row, upper spectral bound, reality, positivity "
                        + "or uniqueness premise is added.")),
                    Paragraph(Text(
                        "Equal amplitudes are load-bearing: z=J/F is unit-valued and exact DC "
                        + "gives z(0)=1. The raw residual factors exactly as "
                        + "F(k)F(1)conj(F(k+1)) times (z(k)z(1)conj(z(k+1))-1). "
                        + "Thus each phase chord is bounded by delta=epsilon/(|F(1)|m^2), "
                        + "which is at most epsilon/m^3<=1/4. For a principal angle theta, "
                        + "d=|exp(i theta)-1|=2|sin(theta/2)|. Real.le_tan together with "
                        + "cos(theta/2)^2>=63/64 gives |theta|<=8d/sqrt(63), preserving the "
                        + "half-angle factor 2. Consuming the complete-cycle theorem gives phase "
                        + "error at most 4(N-1)delta/sqrt(63). Its square produces the exact 16/63.")),
                    Paragraph(Text(
                        "The Fourier residual is (z(k)-stdAddChar(-(k*t)))F(k), and its DC value "
                        + "is exactly zero. The original public FullBispectrumStability.dft_translation "
                        + "identifies the actual signal f(x-t); its cyclic_parseval converts counting "
                        + "squared error to (1/N) times spectral squared error. Removing DC leaves "
                        + "precisely E_F. Internally delta retains |F(1)|^2m^4 in the denominator; "
                        + "|F(1)|>=m supplies the stated m^6 bound. N=1, epsilon=0 and the inclusive "
                        + "epsilon=m^3/4 endpoint are all included. No smallness of N*epsilon is used.")),
                    Paragraph(Text(
                        "This is a source-conditioned equal-amplitude unit. The target-free "
                        + "unequal-amplitude theorem using both zero and generator rows remains open "
                        + "as a separate unit. The order-nine source-uniform obstruction is compatible "
                        + "with this estimate because source energy is allowed to grow. These are "
                        + "repository-derived proofs with direct Mathlib and repository reuse; no "
                        + "literature novelty claim is made. Model proof plans are not kernel evidence."))),
                DescribeRole.Theorem))));
}
