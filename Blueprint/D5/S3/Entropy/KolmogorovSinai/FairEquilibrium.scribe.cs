using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.KolmogorovSinai;

internal sealed class FairEquilibriumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/morgenstern2026ks");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FairEquilibrium", H("Fair Equilibrium"), Blocks(
            Paragraph(Text("The coordinate partition generates the Borel sigma-algebra. The supplier generator theorem reduces the genuine KS supremum to its entropy rate. The entropy bound and the attained Bernoulli value are log 2. Equality forces the maximum entropy value for every finite-word distribution. Existing EntropyEquality gives uniform word masses; the cylinder pi-system determines the law. Measurable conjugacy transports both the invariant measure and the full KS supremum to positive source indices and symbols 1,2. Thus the same source-space fair law is the unique KS maximizer. No target existence or zero-deficit bridge is assumed.")),
            Describe.Lean(DescribeId.Create("fair"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair"),
                H("fair"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fair-invariant"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair_invariant"),
                H("fair invariant"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ks-le"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.ks_le"),
                H("ks le"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fair-ks"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair_ks"),
                H("fair ks"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("max-unique"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.max_unique"),
                H("max unique"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Theorem))));
}
