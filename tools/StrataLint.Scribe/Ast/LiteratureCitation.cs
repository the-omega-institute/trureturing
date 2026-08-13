using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record LiteratureCitation
{
    private LiteratureCitation(string authors, int year, string title, Doi doi)
    {
        Authors = authors;
        Year = year;
        Title = title;
        Doi = doi;
    }

    public string Authors { get; }

    public int Year { get; }

    public string Title { get; }

    public Doi Doi { get; }

    public static LiteratureCitation Create(
        string authors,
        int year,
        string title,
        string doi)
    {
        RequireCanonicalLine(authors, nameof(authors));
        RequireCanonicalLine(title, nameof(title));
        if (year is < 1000 or > 9999)
        {
            throw new ArgumentOutOfRangeException(nameof(year));
        }

        if (!StrataLint.Engine.Doi.TryCreate(doi, out var parsedDoi))
        {
            throw new ArgumentException("Citation DOI is not canonical.", nameof(doi));
        }

        return new LiteratureCitation(authors, year, title, parsedDoi);
    }

    private static void RequireCanonicalLine(string value, string parameter)
    {
        if (string.IsNullOrWhiteSpace(value)
            || !string.Equals(value, value.Trim(), StringComparison.Ordinal)
            || value.IndexOfAny(['\r', '\n']) >= 0)
        {
            throw new ArgumentException(
                "Citation fields must be canonical non-empty lines.",
                parameter);
        }
    }
}
