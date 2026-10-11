using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class GeneratorRowInstabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive real inverse Fourier signals separate bounded generator observations from counting-norm stability.",
        H("Generator Row Instability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("order-nine-parameter-family"),
                DeclarationHandle.Create("D5/S3/Fourier/GeneratorRowInstability.parameter_family"),
                H("A parameter family with exact positive realization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real A>=1 and complex u with |u|=1, use ZMod 9 and the unnormalized "
                        + "negative-exponent Mathlib ZMod.dft. The spectra in index order 0 through 8 are "
                        + "F=(2A+7,1,1,A,1,1,A,1,1) and "
                        + "J=(2A+7,1,u,Au,u,conj(u),Aconj(u),conj(u),1). "
                        + "The signals are the actual inverses ZMod.dft.symm F and ZMod.dft.symm J. "
                        + "Both spectra are Hermitian. The common DC exceeds the sum of all other "
                        + "spectral magnitudes by exactly 1, so both inverse signals are real and "
                        + "at least 1/9 at every point. Every magnitude is at least 1; all magnitudes "
                        + "agree, the source DC dominates, and DC calibration is exact.")),
                    Paragraph(Text(
                        "For B(F;k,l)=F(k)F(l)conj(F(k+l)), every zero-row entry agrees. The signed "
                        + "generator residual B(J;k,1)-B(F;k,1) is conj(u)-1 at k=1 and k=7, "
                        + "u^2-1 at k=4, and zero at all remaining indices, including wraparound k=8. "
                        + "Thus its norm is at most max(|u-1|,|u^2-1|), independently of A. "
                        + "The large amplitudes lie inside constant phase blocks; phase jumps occur "
                        + "only between unit amplitudes.")),
                    Paragraph(Text(
                        "For every t in ZMod 9, the counting squared signal error "
                        + "sum_x |g(x)-f(x-t)|^2 is at least A^2|u^3-1|^2/81. At frequency 3 "
                        + "the translation value z has |z|=1 and z^3=1. Cubic factorization gives "
                        + "|u^3-1|<=3|u-z|. The Fourier discrepancy there is A(u-z), and counting "
                        + "Parseval contributes a factor 1/9. The proof directly reuses the original "
                        + "FullBispectrumStability.cyclic_parseval and dft_translation declarations. "
                        + "The endpoints A=1 and u=1 remain included; the latter gives a zero "
                        + "separation bound without imposing artificial nondegeneracy.")),
                    Paragraph(Text(
                        "The omitted full-bispectrum entry (3,3) has signed residual A^3(u^3-1). "
                        + "The construction therefore supplies no small full-bispectrum-error "
                        + "hypothesis. Its obstruction concerns the zero row and one generator row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-uniform-generator-row-refutation"),
                DeclarationHandle.Create("D5/S3/Fourier/GeneratorRowInstability.result"),
                H("No finite source-independent counting-norm constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Fourier/bendory2017bispectrum")),
                Blocks(
                    Paragraph(Text(
                        "The closed Prop claim asks for one real C>=0 working for all actual positive "
                        + "real signals on ZMod 9 with pointwise lower bound 1/9, exact DC calibration, "
                        + "equal full spectral magnitudes bounded below by 1, source DC dominance, "
                        + "exact zero-row agreement and generator error at most epsilon=64/257. "
                        + "It requires some translation with counting squared error at most C^2epsilon^2. "
                        + "The designated result has the literal type Not claim.")),
                    Paragraph(Text(
                        "Choose u=(255+32i)/257 and A=27(C+1). Exact rational arithmetic gives |u|=1, "
                        + "|u^2-1|=64/257, |u-1|<=64/257 and "
                        + "Im(u^3)=6209632/16974593>1/3. Hence |u^3-1|>1/3 and every translation "
                        + "has squared error >(C+1)^2>C^2epsilon^2. The tolerance is strictly between "
                        + "0 and 1/4, and C=0 is included. Group order, tolerance, spectral lower "
                        + "bound, signal lower bound and DC margin remain fixed across the family.")),
                    Paragraph(Text(
                        "The common DC value is 54C+61 and varies with C. Exact calibration holds "
                        + "within each pair. This does not refute estimates depending on the source, "
                        + "its DC or its maximum spectral magnitude, nor estimates local to a fixed "
                        + "source. It does not refute exact recovery at zero observation error or "
                        + "the complete-bispectrum theorems. The construction and estimate are "
                        + "repository-derived mathematics; no claim of literature novelty is made. "
                        + "Mathlib supplies the inverse transform and the repository supplies the "
                        + "existing Parseval and translation proofs; ordinary model reasoning is "
                        + "not evidence of Lean verification."))),
                DescribeRole.Theorem))));
}
