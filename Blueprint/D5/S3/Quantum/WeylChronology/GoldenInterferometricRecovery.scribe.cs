using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenInterferometricRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A calibrated ideal fringe recovers the legal golden word at an even known length.",
        H("Range-Safe Golden Interferometric Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-safe-fringe-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/WeylChronology/GoldenInterferometricRecovery.even_golden_factor_recovered_at_safe_setting"),
                H("An explicit calibrated setting"),
                StatementSource.FromAuthor(SafeRecovery()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For length n, safeCoupling is pi divided by 2(n+1)^2, and chronologyFringe is the normalized plus-port probability at analyzer phase pi/2 and relative phase 2*kappa*m.")),
                    Paragraph(Text("The source proves 4|m| is at most n squared and proves the nonzero and no-alias obligations for this coupling. The existing legal-language even-length theorem then recovers the word from this fringe alone.")),
                    Paragraph(Text("At a general known length, a true-letter count and the calibrated fringe suffice. At every odd length the source retains two distinct legal words with equal fringes at every coupling. It recovers word content, not occurrence index or prime identity.")),
                    Paragraph(Text("The conclusion is about ideal probabilities. Repeated preparations, finite-shot estimation, pulse accuracy and visibility are additional experimental obligations. The base golden-recovery PR remains an unmerged candidate dependency."))),
                DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Wavefunctions() =>
        Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(Reals()));
    private static Formula Phase(Formula t) => Call("exp", Seq(F.Id("i"), Cdot, Grp(t)));

    private static Formula SafeRecovery()
    {
        Formula n=F.Id("n"), i=F.Id("i"), j=F.Id("j");
        Formula left=Call("goldenFactor",n,i), right=Call("goldenFactor",n,j);
        Formula k=Call("safeCoupling",n);
        return Disp(Seq(Forall,Sp,n,Comma,i,Comma,j,Colon,Mathbb,Grp(F.Id("N")),Comma,Esc,
            Call("Even",n),Rightarrow,
            Call("chronologyFringe",k,left),Eq,Call("chronologyFringe",k,right),Rightarrow,
            left,Eq,right));
    }
}
