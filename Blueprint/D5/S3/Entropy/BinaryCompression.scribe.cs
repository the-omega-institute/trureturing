using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class BinaryCompressionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/BinaryCompression";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, "Sharp binary conditional entropy and Bayes error frontiers.", "evidence-not-specified-by-formal-manifest", Anchor.ParseCanonical("lit/federmerhav1994entropyerror")),
        H("Sharp conditional entropy and Bayes error"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bayes-error-is-least"),
                DeclarationHandle.Create(Module + ".bayesError_isLeast"),
                H("Posterior decision rule attains the minimum error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fair label and any finite stochastic view, choose the more probable label at each view. The posterior formula gives the least probability of error, including ties."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entropy-bits-eq-conditional-entropy"),
                DeclarationHandle.Create(Module + ".entropyBits_eq_conditionalEntropy"),
                H("The posterior formula gives conditional entropy in bits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The joint law has masses equal to half the compression entries. The posterior expression equals the repository conditional entropy divided by log two. A zero-mass view contributes zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entropy-budget"),
                DeclarationHandle.Create(Module + ".entropy_budget"),
                H("Sharp binary entropy and error inequalities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Entropy/federmerhav1994entropyerror")),
                Blocks(Paragraph(Text("For Bayes error e and conditional entropy H in bits, 2e ≤ H ≤ h₂(e). The lower bound integrates the chord of binary entropy on [0, 1/2], and the upper bound applies sharp finite Fano in the two-label case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entropy-frontiers"),
                DeclarationHandle.Create(Module + ".entropy_frontiers"),
                H("Erasure and symmetric flip attain the bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Entropy/federmerhav1994entropyerror")),
                Blocks(Paragraph(Text("At each entropy H between zero and one, the erasure view has error H/2. The symmetric flip with error t has entropy h₂(t), where t is the unique inverse on [0, 1/2]. The formulas include both endpoints."))),
                DescribeRole.Theorem))));
}
