using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class LopesOliveiraWassersteinRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/lopesoliveira2026transport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LopesOliveiraWassersteinRefutation", H("Lopes Oliveira Wasserstein Refutation"), Blocks(
            Paragraph(Text("The claim ranges over every integer d at least 2, every real Holder potential on the original positive-index full shift, and every Borel probability law, with one finite real c depending on d and the potential. It explicitly requires the unique invariant classical KS variational equilibrium for that same potential. KS entropy is the supremum over all finite measurable partitions of the limiting normalized entropy of their iterated joins. The binary constant potential minus log 2 has the proved actual unique fair Bernoulli equilibrium. Its pressure-maximizing noninvariant comparison law has zero deficit and transport distance at least 1/8, so no real c satisfies the displayed inequality. The contradiction includes negative and zero c. There is no restriction to invariant, absolutely continuous, full-support or Markov comparison laws and no extra logarithmic-integrability hypothesis. This is the literal fixed classical target question of section 8, rather than a replacement equilibrium or a finite-tail surrogate.")),
            Describe.Lean(DescribeId.Create("isclassicalequilibrium"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.IsClassicalEquilibrium"),
                H("IsClassicalEquilibrium"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("isuniqueclassicalequilibrium"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.IsUniqueClassicalEquilibrium"),
                H("IsUniqueClassicalEquilibrium"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.claim"),
                H("claim"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("binary-classical-equilibrium"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.binary_classical_equilibrium"),
                H("binary classical equilibrium"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.result"),
                H("result"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(), DescribeRole.Theorem))));
}
