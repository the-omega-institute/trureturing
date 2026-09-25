namespace StrataLint.TestSupport;

internal sealed partial record CoverSpec
{
    internal bool FreezeTargetModule { get; init; } = true;

    internal bool FrozenTargetInBaseline { get; init; } = true;

    internal string TargetStatementId { get; init; } = FrozenStatementReceiptTestData.Id('a');
}
