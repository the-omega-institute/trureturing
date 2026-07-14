namespace StrataLint.Scribe;

public sealed record AnchorDefinition
{
    internal AnchorDefinition(string name, Anchor anchor, string provenance)
    {
        if (string.IsNullOrWhiteSpace(name))
        {
            throw new ArgumentException("Anchor definition name must be non-empty.", nameof(name));
        }

        Name = name;
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

    public string Name { get; }

    public Anchor Anchor { get; }

    public string Provenance { get; }
}
