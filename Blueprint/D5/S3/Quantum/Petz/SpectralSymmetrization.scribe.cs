using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class SpectralSymmetrizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/SpectralSymmetrization.";
    private const string Summary = "The labelled Dittmann kernel and its cyclic symmetrization, including coincident positive nodes.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("K", true),
        ("d", true),
        ("d_symmetrization", false),
        ("d_self", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("SpectralSymmetrization"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-spectralsymmetrization-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name) => name switch
    {
        "K" => "K is the first derivative of the logarithm of the logarithmic-mean resolvent in its first node.",
        "d" => "d is Dittmann's labelled three-node curvature kernel formed from K and its divided difference.",
        "d_symmetrization" => "The cyclic average of the labelled kernel equals the symmetric kernel on positive nodes, including coincidences.",
        "d_self" => "At a positive triple coincidence, the labelled kernel has the stated diagonal value.",
        _ => "The named spectral identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
