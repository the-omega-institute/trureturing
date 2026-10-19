using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalWindowEvenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original complex AE-even window sector and parity of the symmetric finite prime action.",
        H("Original window even sector"),
        Blocks(
            Paragraph(Text("The carrier WindowL2(a) is complex L2 for Lebesgue measure restricted to Ioc(-a,a]. Evenness is defined by the actual whole-line zero extension before any cosine span is considered. The results in this module allow arbitrary real a; the later normalized cosine completeness and projection estimates require a>0. All mode and prime cutoffs here are natural numbers, and coefficient families are complex.")),
            Describe.Lean(
                DescribeId.Create("zero-isometry"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.zeroIsometry"),
                H("Isometric zero extension of L2 classes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex linear isometry sends the window class to its indicator zero extension in whole-line complex L2. The construction uses the existing interval zero-extension result with length 2*a and origin -a. Its norm equality uses the indicator/restricted-measure identity; no endpoint trace is selected."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-even"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven"),
                H("Original AE-even subspace"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Whole-line reflection is composition with x |-> -x and is complex linear, without conjugating the values. originalEven is the kernel of reflection after zero extension minus zero extension. This definition includes the full original AE-even sector independently of any Fourier or cosine completeness statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-even-closed"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven_isClosed"),
                H("Closedness of the original even sector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sector is closed as the kernel of a continuous complex linear map. Its subtype is therefore complete, supplying the Hilbert-space projection framework used later."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-even-membership"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.mem_originalEven_iff"),
                H("Membership means AE reflection invariance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any window L2 class u, membership is equivalent to equality almost everywhere for whole-line Lebesgue measure between its zero extension at -x and at x. Reflection turns Ioc into Ico; the two exceptional endpoints have measure zero. No pointwise equality of the endpoint indicators is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-even-representative"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven_representative"),
                H("Independence of the chosen representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hypothesis identifies u and a function f almost everywhere for the restricted window measure. Under precisely that hypothesis, membership can be tested using the original zero extension of f. Arbitrary representative values at the endpoints do not change the criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("head-even"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.head_mem_originalEven"),
                H("Every finite complex cosine head is originally even"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each real cosine mode is even, so its complex L2 class lies in the sector. Closure under complex scalar multiplication and finite sums puts headL2(a,N,v), with indices 0 through the natural N, in the same original sector for every complex family v. This inclusion does not assume completeness of the modes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compression-reflection"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.compression_reflection_ae"),
                H("Reflection reverses an actual compressed shift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real a and s and a function whose original zero extension is AE-even, reflecting compression(a,s,f) equals compression(a,-s,f) almost everywhere. Both the inner zero extension before translation and the outer compression to Ioc(-a,a] remain in the identity. Translation preserves the null sets needed for this argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-action-even"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.primeAction_even"),
                H("Parity of the original symmetric finite prime action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any natural cutoff K, the exact sum over r in Icc(1,K) retains weight vonMangoldt(r)/sqrt(r) and both compressed shifts by log(r) and -log(r). AE-evenness of the input zero extension makes their sum AE-even. Prime powers remain present; there is no primality-only filter, real-coefficient restriction or cancellation assumption. The separate support identity says that applying zero extension again leaves this action unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-head-even"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalWindowEven.primeHead_mem_originalEven"),
                H("The actual finite prime image lies in the original even sector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("primeHeadL2 uses the arithmetic cutoff primeCutoff(a)=floor(exp(2*a)), independently of the natural head cutoff N. Its representative is the exact primeAction on the complex cosine profile. The representative criterion, support identity and parity of the paired shifts place that L2 class in originalEven, without any separation condition on N.")),
                    Paragraph(Text("These are applications of standard Lp zero extension, measure-preserving reflection and closed-kernel Hilbert-space methods. They provide analytic parity and carrier facts, with no literature novelty, canonical full Weil arithmetic/operator identification, signed positivity or Riemann-hypothesis conclusion claimed."))),
                DescribeRole.Theorem))));
}
