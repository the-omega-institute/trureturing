namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    private const string RetiredDeliveryStatementAddress =
        "sha256:40f8ddef4656aca501f26e95c45e33dec0fbca857a48c82c9ad7708b21f81011";
    private const string MismatchingRetiredDeliveryStatementAddress =
        "sha256:c1069552fbd47c6fe20f6a7b1cadde8efdf2f782c9cd51f14bc633213d1d76b9";
    private const string LiteralRetiredV2Contract =
        "/- THEORIST_FRONTIER_CONTRACT_V2\n"
        + "{\"schema\":\"trureturing-theorist-frontier-v2\",\"exact_statement\":{\"gid\":\"D5/X_Frontier/PrimeNormIrreducibility.prime_norm_irreducible\",\"statement_sha256\":\""
        + RetiredDeliveryStatementAddress
        + "\"},\"motivation_gids\":[\"D5/S0/Carrier/Euclidean\"],\"falsifier\":\"a finite counterexample fiber\",\"search_receipt_gids\":[\"D5/L/Carrier/fixture2026contract\"],\"computation_receipt_gids\":[\"D5/E/S0/Carrier/Probe.result--json\"],\"triage_class\":\"theorem\"}\n-/";

    internal void ReplaceRetiredBaselineWithLiteralV2Contract() =>
        ReplaceRetiredBaselineContract(LiteralRetiredV2Contract);

    internal void ReplaceRetiredBaselineStatementWithMismatchingLiteralHash() =>
        ReplaceBaselineContract("statement_sha256", MismatchingRetiredDeliveryStatementAddress);

    internal void DuplicateRetiredBaselineContract()
    {
        var source = Baseline[currentTheoristPath];
        var start = source.IndexOf("/- THEORIST_FRONTIER_CONTRACT_V2", StringComparison.Ordinal);
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        Baseline[currentTheoristPath] = source + "\n" + source[start..(end + 3)];
    }

    internal void RemoveRetiredBaselineContractClosingMarker()
    {
        var source = Baseline[currentTheoristPath];
        var start = source.IndexOf("/- THEORIST_FRONTIER_CONTRACT_V2", StringComparison.Ordinal);
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        Baseline[currentTheoristPath] = source[..end] + "\n--/" + source[(end + 3)..];
    }

    internal void CorruptRetiredBaselineContractCanonicalForm(string corruption)
    {
        var source = Baseline[currentTheoristPath];
        var start = source.IndexOf("/- THEORIST_FRONTIER_CONTRACT_V2", StringComparison.Ordinal);
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        var contract = source[start..(end + 3)];
        var corrupted = corruption switch
        {
            "keys" => contract.Replace(
                "\"triage_class\":",
                "\"unexpected\":true,\"triage_class\":",
                StringComparison.Ordinal),
            "schema" => contract.Replace(
                "trureturing-theorist-frontier-v2",
                "trureturing-theorist-frontier-v3",
                StringComparison.Ordinal),
            "hash" => contract.Replace(
                "\"statement_sha256\":\"sha256:",
                "\"statement_sha256\":\"sha256:0",
                StringComparison.Ordinal),
            _ => throw new ArgumentOutOfRangeException(nameof(corruption)),
        };
        Assert.NotEqual(contract, corrupted);
        Baseline[currentTheoristPath] = source[..start] + corrupted + source[(end + 3)..];
    }
}
