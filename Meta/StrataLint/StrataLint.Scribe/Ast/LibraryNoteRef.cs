using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record LibraryNoteRef
{
    private LibraryNoteRef(GidRef reference, BibKey bibKey)
    {
        Reference = reference;
        BibKey = bibKey;
        Anchor = new LiteratureAnchor(bibKey);
    }

    public GidRef Reference { get; }

    public string Value => Reference.Value;

    public BibKey BibKey { get; }

    public LiteratureAnchor Anchor { get; }

    public static LibraryNoteRef Create(string value)
    {
        var reference = GidRef.Create(value);
        if (!reference.IsLibrary)
        {
            throw new ArgumentException("Value must be a Library-plane GID.", nameof(value));
        }

        var rawBibKey = value[(value.LastIndexOf('/') + 1)..];
        var bibKey = BibKey.TryCreate(rawBibKey)
            ?? throw new ArgumentException("Library GID needs a canonical bibkey.", nameof(value));
        return new LibraryNoteRef(reference, bibKey);
    }

    public override string ToString() => Value;
}
