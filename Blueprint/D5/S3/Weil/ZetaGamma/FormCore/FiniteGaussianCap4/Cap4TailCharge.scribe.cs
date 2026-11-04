using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class Cap4TailChargeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4TailCharge.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete infinite tail charge control",
        H("Complete infinite tail charge control"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cap4-complete-tail-reciprocal"),
                DeclarationHandle.Create(Owner + "complete_tail_reciprocal_bound"),
                H("The whole reciprocal-energy tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let w(0)=1 and w(k+1)=w(k)*(k+9/4)*(k+1/2)/((k+11/4)*(k+1)). Set H(k)=((2*k+9/4)^2-440)/10-3/4. The entire series over k>=16 of w(k)/H(k) is summable and at most S=1028725771676171625/157438844598004744192.")),
                    Paragraph(Text("The proof constructs a positive telescoping potential w(k)*(1+(k+9/4)/2)/H(k). Its one-step debit dominates w(k)/H(k) for every k>=16, using an explicit shifted cubic with positive coefficients. Finite prefixes retain their final nonnegative potential before passing to the infinite sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cap4-complete-tail-charge"),
                DeclarationHandle.Create(Owner + "complete_tail_charge_bound"),
                H("Energy summability proves charge convergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real sequence u indexed from zero, assume only summability of H(16+n)*w(16+n)*u(n)^2. Then w(16+n)*u(n) is summable and rho*(sum_n w(16+n)*u(n))^2 is at most sum_n H(16+n)*w(16+n)*u(n)^2, where rho=1/S. The index n=0 corresponds to mode 16.")),
                    Paragraph(Text("The preceding reciprocal-tail estimate supplies the new analytic input to finite Cauchy-Schwarz bounds and their limit. Charge convergence is proved from energy summability. This sequence theorem assumes no physical Gaussian expansion and establishes no final spectral quotient or RH statement. The estimates are repository-derived; standard summability and Cauchy-Schwarz theorems are reused."))),
                DescribeRole.Theorem))));
}
