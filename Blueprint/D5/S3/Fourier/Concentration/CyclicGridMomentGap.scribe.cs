using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicGridMomentGapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicGridMomentGap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real projection variance controls separation from orthogonality.",
        H("Phase separation and Fourier moment variance"),
        Blocks(
            Paragraph(Text(
                "Write m and b for a first and a second complex moment. Let c be the squared "
                + "magnitude of m, s the product c(1−c), and D the real projection variance "
                + "c/2−c²+Re(conjugate(m)² b)/2. Given the separation δ, let "
                + "d be the maximum of δ−|2c−1| and zero.")),
            Describe.Lean(
                DescribeId.Create("phase-separation-variance-bound"),
                DeclarationHandle.Create(Owner + ".phase_separation_variance_bound"),
                H("The variance bound for separated unit phases"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a finite indexed family of complex unit phases z and nonnegative "
                        + "real weights w that sum to one. Let m be the weighted sum of the phases "
                        + "and b the weighted sum of their squares. For each pair of indices "
                        + "with positive weight, assume the absolute real part of the product "
                        + "of one phase and the conjugate of the other is at least δ.")),
                    Paragraph(Text(
                        "A diagonal pair bounds δ by one, so positive d implies c lies strictly "
                        + "between zero and one. Rotate and scale by the conjugate of m. The "
                        + "stability estimates "),
                        Ref("D5/S3/Fourier/Concentration/CyclicMomentStability.first_two_moment_stability"),
                        Text(" control squared error to the two comparison phases and the "
                        + "difference of the sign-class masses. Averaging the squared perturbation "
                        + "of the real inner product over pairs from opposite classes gives "
                        + "ab c d² at most the total squared error, with a,b the class masses. "
                        + "Substitute four times their product as one minus the squared mass "
                        + "difference to get the claimed inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-grid-fourier-gap"),
                DeclarationHandle.Create(Owner + ".cyclic_grid_fourier_gap"),
                H("The variance bound on a cyclic grid"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a positive integer with four not dividing q and w a real "
                        + "probability weight on the residues. Let m and b be the coefficients "
                        + "at residues one and two of the unnormalized DFT with negative phase. "
                        + "Take δ=sin(pi/(2q)) for odd q and δ=sin(pi/q) for even q.")),
                    Paragraph(Text(
                        "For an integer difference k of residues, center 4k−q modulo 2q. "
                        + "The centered integer has absolute value at least one for odd q "
                        + "and at least two for even q. Sine monotonicity gives the required "
                        + "bound on the absolute real product of the two character values. "
                        + "The phase variance theorem then gives the result with those moments. "
                        + "A positive-resolution bound at growing order for actual zeta "
                        + "ordinates remains open."))),
                DescribeRole.Theorem))));

    private static Formula Bound()
    {
        var c = F.Id("c");
        var d = F.Id("d");
        var s = F.Id("s");
        var cd2 = Multiply(c, new Formula.Power(d, D(2)));
        var coefficient = Seq(Open, D(1), Plus, new Formula.Fraction(D(4), s), Plus,
            new Formula.Fraction(cd2, new Formula.Power(s, D(2))), Close);
        return Disp(Seq(D(0), Sp, Lt, Sp, d, Sp, Implies, Sp, cd2, Sp, Leq, Sp,
            Multiply(Multiply(D(4), coefficient), F.Id("D"))));
    }
}
