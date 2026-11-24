using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicMomentStabilityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicMomentStability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real projection variance controls two phase errors from a common probability weight.",
        H("Stability from Two Fourier Moments"),
        Blocks(
            Paragraph(Text(
                "Take a finite indexed family of complex unit phases z(j) with nonnegative real "
                + "weights w(j) of total mass one. Let m be the weighted first moment, b the weighted "
                + "second moment, and c the squared magnitude of m. Set X(j) to the conjugate of m "
                + "times z(j). Suppose c lies strictly between zero and one. Let t be the positive "
                + "square root of c(1−c). Let eta(j) equal 1 at a nonnegative imaginary part of X(j) "
                + "and −1 at a negative imaginary part. Define D as c/2 minus c squared plus half "
                + "the real part of the product of b and the squared conjugate of m.")),
            Describe.Lean(
                DescribeId.Create("first-two-moment-stability"),
                DeclarationHandle.Create(Owner + ".first_two_moment_stability"),
                H("Phase error and mass balance"),
                StatementSource.FromAuthor(Stability()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The weighted mean of X is c and its imaginary mean is zero. The unit-circle "
                    + "identity and the second moment identify D with the weighted variance of the "
                    + "real part of X. Write x and y for the real and imaginary parts at one index. "
                    + "The squared imaginary magnitudes obey y squared minus t squared equal to "
                    + "c squared minus x squared. Factoring and using |x+c| at most two bounds "
                    + "the squared imaginary error by 4/t squared times the squared real error. "
                    + "Summing and using the weighted Cauchy–Schwarz inequality gives the two bounds.")),
                    Paragraph(Text(
                        "The interval for c gives two distinct comparison points and a positive "
                        + "divisor. The unit-phase condition gives the pointwise norm identity. "
                        + "Nonnegative weights allow the pointwise estimates to be summed, and mass "
                        + "one fixes the mean and the Cauchy–Schwarz factor. When b=0, D becomes "
                        + "c/2 minus c squared. At c=1/2 this forces both errors to vanish. The "
                        + "comparison points lie on the scaled unit circle. A quantitative separation "
                        + "estimate for a discrete cyclic grid and a bound for weighted near-collisions "
                        + "of actual zeta ordinates at growing order remain separate questions."))),
                DescribeRole.Theorem))));

    private static Formula Stability()
    {
        var j = F.Id("j");
        var c = F.Id("c");
        var t = F.Id("t");
        var Dv = F.Id("D");
        var weight = Call("w", j);
        var sign = Call("eta", j);
        var sum = new Formula.Subscript(Sum, j);
        var error = new Formula.Absolute(Seq(Call("X", j), Minus, c, Minus,
            Multiply(Multiply(F.Id("i"), sign), t)));
        var phaseError = Seq(sum, Sp, Multiply(weight, new Formula.Power(error, D(2))));
        var phaseBound = Multiply(Seq(Open, Add(D(1),
            new Formula.Fraction(D(4), new Formula.Power(t, D(2)))), Close), Dv);
        var balance = new Formula.Power(Seq(Open, sum, Sp, Multiply(weight, sign), Close), D(2));
        var balanceBound = new Formula.Fraction(Multiply(D(4), Dv), new Formula.Power(t, D(4)));
        return Disp(Seq(phaseError, Sp, Leq, Sp, phaseBound, Sp, Land, Sp,
            balance, Sp, Leq, Sp, balanceBound));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
