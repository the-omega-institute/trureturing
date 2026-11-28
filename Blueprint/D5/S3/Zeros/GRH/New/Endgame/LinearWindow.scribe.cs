using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Endgame;

internal sealed class LinearWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed moments and linear windows", H("Signed moments and linear windows"),
        Blocks(
            Describe.Lean(DescribeId.Create("signed-moment-linear-window"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Endgame/LinearWindow.exists_linear_window_sub_mul_le"),
                H("A uniform good scale in a linear window"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let E and F be polar real error functions, with respective transforms r and s in the sense of IsPolar. Their factorial moment theorem supplies one common real radius R with 3 < R < 4. For each function H in {E,F}, for every sufficiently large real t, both of the following hold: |H(v)| is at most t exp(v) for every v at least zero; and, for every natural k, v^k exp(-3v) H(v) is integrable on (0,infinity), with the absolute value of its signed integral at most k! t/R^k. The eventual thresholds may differ between E and F.")),
                    Paragraph(Text("Then there is a real constant C > 1 such that, for every sufficiently large real t and every real X with 0 <= X <= exp(t), some real u satisfies t <= u <= Ct and E(u) - X F(u) <= exp(-t). The threshold for t is uniform in X. The moment hypothesis bounds the absolute value of a signed integral, rather than the integral of the absolute value.")),
                    Paragraph(Text("Choose delta = log(R)-log(3), C = 99/delta and k = ceil(Ct/9). If the conclusion fails on [t,Ct], add two positive exponential tails to exp(-3v)(E(v)-XF(v)-exp(-t)). Their sum is nonnegative on v > 0. Integration against v^k gives two positive tail contributions and an upper bound on the signed-moment contribution, each smaller than one third of k! exp(-t)/3^(k+1), contradicting the negative constant contribution.")),
                    Paragraph(Text("The signed-moment selection theorem is Omega.Analysis.exists_linear_window_of_signed_moments. Its proof uses only exponential envelopes and signed moments. The polar-function moment estimates in OneSidedCriterion supply these analytic inputs, strengthening the quadratic second-scale window to a linear window for the same two polar errors. It is an analytic selection lemma; it does not by itself establish a prime-error bound or a complete proof of the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
