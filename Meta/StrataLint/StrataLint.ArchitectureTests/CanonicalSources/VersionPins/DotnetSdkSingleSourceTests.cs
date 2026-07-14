namespace StrataLint.ArchitectureTests;

public sealed class DotnetSdkSingleSourceTests
{
    [Fact]
    public void WorkflowReadsDotnetSdkPinsFromGlobalJson()
    {
        var findings = DotnetSdkSingleSourcePolicy.InspectRepository(
            RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(
                Environment.NewLine,
                findings.Select(static finding => $"{finding.Path}: {finding.Message}")));
    }

    [Fact]
    public void CopiedDotnetVersionIsRejectedByTheRedFixture()
    {
        const string workflow = """
            jobs:
              test:
                steps:
                  - uses: Actions/Setup-Dotnet@v4
                    with:
                      dotnet-version: 10.0.103
            """;

        var findings = DotnetSdkSingleSourcePolicy.InspectWorkflow(
            ".github/workflows/synthetic.yml",
            workflow);

        Assert.Contains(findings, static finding =>
            finding.Message.Contains("copies the SDK version", StringComparison.Ordinal));
        Assert.Contains(findings, static finding =>
            finding.Message.Contains("global-json-file", StringComparison.Ordinal));
    }

    [Fact]
    public void GlobalJsonReferenceIsAccepted()
    {
        const string workflow = """
            jobs:
              candidate:
                steps:
                  - uses: actions/setup-dotnet@v4
                    with:
                      global-json-file: candidate/global.json
              baseline:
                steps:
                  - uses: actions/setup-dotnet@v4
                    with:
                      global-json-file: baseline/global.json
            """;

        Assert.Empty(DotnetSdkSingleSourcePolicy.InspectWorkflow(
            ".github/workflows/synthetic.yml",
            workflow));
    }

    [Fact]
    public void MissingBaselineGlobalJsonReferenceIsRejectedByTheRedFixture()
    {
        const string workflow = """
            jobs:
              candidate:
                steps:
                  - uses: actions/setup-dotnet@v4
                    with:
                      global-json-file: candidate/global.json
            """;

        var finding = Assert.Single(DotnetSdkSingleSourcePolicy.InspectWorkflow(
            ".github/workflows/synthetic.yml",
            workflow));

        Assert.Contains("baseline/global.json", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AdditionalWorkflowCopiedDotnetVersionIsRejectedByTheRedFixture()
    {
        var root = Directory.CreateTempSubdirectory("stratalint-sdk-single-source-").FullName;
        try
        {
            var workflows = Path.Combine(root, ".github", "workflows");
            Directory.CreateDirectory(workflows);
            File.WriteAllText(Path.Combine(workflows, "ci.yml"), """
                jobs:
                  candidate:
                    steps:
                      - uses: actions/setup-dotnet@v4
                        with:
                          global-json-file: candidate/global.json
                  baseline:
                    steps:
                      - uses: actions/setup-dotnet@v4
                        with:
                          global-json-file: baseline/global.json
                """);
            File.WriteAllText(Path.Combine(workflows, "release.yaml"), """
                jobs:
                  release:
                    steps:
                      - uses: actions/setup-dotnet@v4
                        with:
                          global-json-file: release/global.json
                          dotnet-version: 99.0.1
                """);

            var finding = Assert.Single(
                DotnetSdkSingleSourcePolicy.InspectRepository(root));

            Assert.Equal(".github/workflows/release.yaml", finding.Path);
            Assert.Contains("copies the SDK version", finding.Message, StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }
}
