namespace StrataLint.Engine;

public sealed record AnchorDefinition
{
    internal AnchorDefinition(Anchor anchor, string provenance)
    {
        Anchor = anchor ?? throw new ArgumentNullException(nameof(anchor));
        if (string.IsNullOrWhiteSpace(provenance)
            || provenance.Contains('\r', StringComparison.Ordinal)
            || provenance.Contains('\n', StringComparison.Ordinal))
        {
            throw new ArgumentException(
                "Anchor provenance must be one non-empty line.",
                nameof(provenance));
        }

        Provenance = provenance;
    }

    public Anchor Anchor { get; }

    public string Provenance { get; }
}
