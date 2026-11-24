using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicGridMomentGapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicGridMomentGap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separation from orthogonality improves the first-moment bound for a small second moment.",
        H("First-moment gap for separated phase supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-moment-gap-of-small-second"),
                DeclarationHandle.Create(Owner + ".first_moment_gap_of_small_second"),
                H("A quantitative gap from pairwise phase separation"),
                StatementSource.FromAuthor(Gap("m")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let z be a finite indexed family of complex unit phases with real "
                        + "weights w that are nonnegative and sum to one. Write m for the weighted "
                        + "sum of the phases and b for the weighted sum of the squared phases. "
                        + "Set epsilon to the magnitude of b and take a positive real delta. "
                        + "For every pair of indices with "
                        + "positive weight, assume the absolute real part of the first phase times "
                        + "the conjugate of the second phase is at least delta.")),
                    Paragraph(Text(
                        "A positive-weight diagonal pair gives delta at most one. Centering the "
                        + "second moment and applying the triangle inequality gives the upper "
                        + "bound (1+epsilon)/2 before imposing separation. The already "
                        + "proved stability estimates for the same weights "),
                        Ref("D5/S3/Fourier/Concentration/CyclicMomentStability.first_two_moment_stability"),
                        Text(" force at least one positive-weight phase close to each of two "
                        + "comparison points if the deficit is too small. The real inner product "
                        + "of those points is controlled by the deficit and epsilon. Bounding the changes "
                        + "in that product gives a pair whose real inner product has absolute "
                        + "value strictly below delta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-grid-fourier-gap"),
                DeclarationHandle.Create(Owner + ".cyclic_grid_fourier_gap"),
                H("Explicit angular separation on a cyclic grid"),
                StatementSource.FromAuthor(Gap("a")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a positive integer modulus q that is not divisible by four. "
                        + "Let w be a nonnegative real weight of mass one on the residues "
                        + "modulo q. Compute its unnormalized discrete Fourier transform with "
                        + "the negative phase. Write epsilon for the magnitude of the coefficient "
                        + "at residue two and a for the coefficient at residue one. Take delta to be "
                        + "sin(pi/(2q)) for odd q and sin(pi/q) for even q.")),
                    Paragraph(Text(
                        "For each integer difference d of residues, reduce 4d−q to a centered "
                        + "residue modulo 2q. It cannot vanish because q is not divisible by four. "
                        + "Its absolute value is at least one when q is odd and at least two when "
                        + "q is even. Apply sine monotonicity on the resulting interval between "
                        + "zero and pi/2 to bound the absolute cosine of the phase difference. "
                        + "The finite-phase theorem then applies to the standard additive character. "
                        + "At zero second coefficient the bound is 1/2 minus delta squared over 1024. "
                        + "The separation hypothesis concerns a fixed finite support. A weighted "
                        + "positive-resolution bound at growing order for actual zeta ordinates "
                        + "remains open."))),
                DescribeRole.Theorem))));

    private static Formula Gap(string moment)
    {
        var magnitude = new Formula.Absolute(F.Id(moment));
        var squaredGap = new Formula.Power(DeltaLower, D(2));
        var epsilon = Varepsilon;
        return Disp(Seq(epsilon, Sp, Leq, Sp, new Formula.Fraction(DeltaLower, D(8)), Sp,
            Implies, Sp, new Formula.Power(magnitude, D(2)), Sp, Leq, Sp,
            new Formula.Fraction(Add(D(1), epsilon), D(2)), Minus,
            new Formula.Fraction(squaredGap, D(1, 0, 2, 4))));
    }
}
