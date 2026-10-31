namespace StrataLint.CliIntegration.Tests;

internal static class AdmissionStandardError
{
    internal static void AssertOnlyTimingEvents(byte[] standardError) => Assert.Empty(standardError);
}
