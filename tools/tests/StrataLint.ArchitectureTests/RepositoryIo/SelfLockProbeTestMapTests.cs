namespace StrataLint.ArchitectureTests;

public sealed class SelfLockProbeTestMapTests
{
    [Fact]
    public void EverySelfLockProbeTestMethodHasKnownRepositoryInputs()
    {
        var methods = ScribeTestMapDeriver.DeriveRepository(RepositoryLayout.FindRoot())
            .Methods
            .Where(static method => method.Id.StartsWith(
                "SelfLockProbeScriptTests.",
                StringComparison.Ordinal))
            .ToArray();

        Assert.NotEmpty(methods);
        Assert.All(
            methods,
            static method => Assert.False(
                method.IsUnknown,
                $"{method.DisplayIdentity}: {string.Join(',', method.UnknownReasons)}"));
    }
}
