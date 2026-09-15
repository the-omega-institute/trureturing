using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record LiteratureCitation
{
    private LiteratureCitation(string authors, int year, string title, Doi? doi, Uri? url)
    {
        Authors = authors;
        Year = year;
        Title = title;
        Doi = doi;
        Url = url;
    }

    public string Authors { get; }

    public int Year { get; }

    public string Title { get; }

    public Doi? Doi { get; }

    public Uri? Url { get; }

    public static LiteratureCitation Create(
        string authors,
        int year,
        string title,
        string? doi,
        string? url = null)
    {
        RequireCanonicalLine(authors, nameof(authors));
        RequireCanonicalLine(title, nameof(title));
        if (year is < 1000 or > 9999)
        {
            throw new ArgumentOutOfRangeException(nameof(year));
        }

        Doi? parsedDoi = null;
        if (doi is not null && !StrataLint.Engine.Doi.TryCreate(doi, out parsedDoi))
        {
            throw new ArgumentException("Citation DOI is not canonical.", nameof(doi));
        }

        var parsedUrl = url is null ? null : ParseStableUrl(url);
        if (parsedDoi is null && parsedUrl is null)
        {
            throw new ArgumentException("Citation requires a DOI or URL.");
        }

        return new LiteratureCitation(authors, year, title, parsedDoi, parsedUrl);
    }

    internal static Uri ParseStableUrl(string value)
    {
        RequireCanonicalLine(value, nameof(value));
        if (!Uri.TryCreate(value, UriKind.Absolute, out var uri)
            || uri.Scheme != Uri.UriSchemeHttps
            || uri.Host.Length == 0
            || uri.UserInfo.Length != 0
            || !Uri.IsWellFormedUriString(value, UriKind.Absolute)
            || !string.Equals(value, uri.AbsoluteUri, StringComparison.Ordinal))
        {
            throw new ArgumentException("Literature URL must be a canonical absolute HTTPS URL.");
        }

        return uri;
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
