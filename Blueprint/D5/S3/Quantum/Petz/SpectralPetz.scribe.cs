using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class SpectralPetzDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/SpectralPetz.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Petz's spectral monotonicity theorem for faithful ordered spectra.",
        H("SpectralPetz"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-spectralpetz-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("claim"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("claim states that a faithful decreasing spectrum with smaller prefix sums has no larger ordered spectral curvature sum than the more mixed faithful spectrum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-spectralpetz-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("result"),
                StatementSource.FromAuthor(Disp(F.Id("result"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The result follows by identifying spectralS with spectralHs, applying the ordered pair-transfer reduction, and using the four Dittmann inequalities for the transfer derivative."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("petz-1994-bkm-scalar-curvature-monotonicity"), ResolutionKind.Proved)))));
}
