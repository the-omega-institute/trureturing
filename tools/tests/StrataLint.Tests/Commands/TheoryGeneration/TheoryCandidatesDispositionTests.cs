using System.Text.Json;

namespace StrataLint.Tests;

public sealed partial class TheoryCandidatesTests
{
    [Fact]
    public void DispositionedAtomIsVisiblyWithheldFromTheoryCandidates()
    {
        var fixture = CandidateFixture();
        fixture.Files[ResidualAtomPath] = fixture.Files[ResidualAtomPath].Replace(
            "  tail_authorization: null",
            """
              tail_authorization: null
              cover_disposition:
                outcome: partial-closed
                recorded_at_utc: 2026-08-25T04:03:02.0000000+00:00
                gids:
                  - D5/S0/Carrier/Probe.probe
                gaps:
                  - code: unresolved-subitem
                    detail: remaining theorem clause
            """,
            StringComparison.Ordinal);

        var result = Run(fixture);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.DoesNotContain(
            json.RootElement.GetProperty("candidates").EnumerateArray(),
            static candidate => candidate.GetProperty("candidate_id").GetString() == "atom/fixture-atom");
        var withheld = Assert.Single(json.RootElement.GetProperty("withheld").EnumerateArray());
        Assert.Equal("atom/fixture-atom", withheld.GetProperty("candidate_id").GetString());
        Assert.Equal("digestion_atom", withheld.GetProperty("source_kind").GetString());
        Assert.Equal("fixture-atom", withheld.GetProperty("source_ref").GetString());
        Assert.Equal("cover-disposition", withheld.GetProperty("withhold_reason").GetString());
    }
}
