using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FisherDiscord;

internal sealed class ExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FisherDiscord/Extension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flagged extensions of diagonal density matrices have zero Fisher discord.",
        H("Flagged Fisher-discord extensions"), Blocks(
            Item("flagExtension", "Classical flag extension",
                "For a finite diagonal weight function w, the flagged matrix places w(i) on the product basis vector (i,i) and zero elsewhere. The second factor records the first-factor index.", DescribeRole.Definition),
            Item("flag_partialTrace", "Flag marginal",
                "Taking the second-factor partial trace of the flagged matrix returns the diagonal matrix with entries w(i).", DescribeRole.Theorem),
            Item("flag_discord_zero", "Zero discord of a flag",
                "For nonnegative weights, every Hermitian SLD solution on the flagged matrix gives zero Fisher discord for an observable lifted from the first factor.", DescribeRole.Theorem),
            Item("extensionIneq", "Extension inequality",
                "The extension inequality compares the discord of a fixed diagonal marginal and observable with every state having that marginal and every admissible Hermitian SLD.", DescribeRole.Definition),
            Item("monotone_iff_discord_zero", "Classification of diagonal marginals",
                "For normalized nonnegative diagonal weights, a Hermitian observable, a marginal SLD solution and an SLD existence witness for the flag, the extension inequality holds in every finite second dimension exactly when the marginal Fisher discord is zero. The extensions themselves need not be diagonal.", DescribeRole.Theorem))));

    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name switch
        {
            "flagExtension" => "fisher-discord-extension-flag-extension",
            "flag_partialTrace" => "fisher-discord-extension-flag-partial-trace",
            "flag_discord_zero" => "fisher-discord-extension-flag-discord-zero",
            "extensionIneq" => "fisher-discord-extension-extension-ineq",
            _ => "fisher-discord-extension-monotone-iff-discord-zero"
        }),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
