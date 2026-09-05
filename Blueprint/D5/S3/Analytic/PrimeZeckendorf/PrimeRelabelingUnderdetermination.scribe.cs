using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeZeckendorf;

internal sealed class PrimeRelabelingUnderdeterminationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/PrimeZeckendorf/PrimeRelabelingUnderdetermination.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden depth and Zeckendorf structure are invariant under arbitrary prime relabeling, so canonical prime localization requires additional arithmetic rigidity.",
        H("Prime-Relabeling Underdetermination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("layer-readout-is-prime-relabeling-invariant"),
                DeclarationHandle.Create(Prefix
                    + "layer_readout_prime_relabeling_invariant"),
                H("Layer observation cannot distinguish prime relabeling"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), Comma, Sp,
                    Operatorname, Grp(F.Id("layerReadout")), Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("primeRelabeling")), Open, F.Id("r"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("layerReadout")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every equivalence of the prime type can relabel the local coordinate while leaving the entire golden layer coordinate unchanged.")),
                    Paragraph(Text(
                        "The same relabeling also preserves the Zeckendorf component. Thus layer geometry alone cannot canonically identify which local label is the arithmetic prime two, three, five, and so on."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-readout-separates-prime-relabelings"),
                DeclarationHandle.Create(Prefix
                    + "prime_readout_separates_prime_relabelings"),
                H("The explicit prime readout has relabeling rigidity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("SeparatesPrimeRelabelings")),
                    Open,
                    Operatorname, Grp(F.Id("primeReadout")),
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An observable satisfies the new rigidity criterion when invariance under a prime relabeling forces every prime to be fixed.")),
                    Paragraph(Text(
                        "The explicit prime projection satisfies this condition. A future geometric-to-prime map must establish comparable rigidity from valuation, norm, divisibility, adelic, or spectral structure rather than by attaching anonymous labels."))),
                DescribeRole.Theorem))));
}
