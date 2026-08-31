using StrataLint.EngineeringScope;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class TestResultEvidenceTests
{
    [Fact]
    public void CountAssemblyFiltersExecutedIdentitiesCaseInsensitively()
    {
        var evidence = new TestResultEvidence(
            3,
            new HashSet<(string Assembly, string Id)>
            {
                ("StrataLint.EngineeringScope.Tests", "First"),
                ("stratalint.engineeringscope.tests", "Second"),
                ("StrataLint.Tests", "Third"),
            });
        var counts = new[]
        {
            "STRATALINT.ENGINEERINGSCOPE.TESTS",
            "StrataLint.Scribe.Tests",
        }.Select(evidence.CountAssembly).ToArray();

        Assert.Equal([2, 0], counts);
    }

    [Fact]
    public void RejectsWhenAProtectedBasePlannedIdentityWasNotExecuted()
    {
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("First.Owner.Tests", "PlannedTests.Executed"),
            });
        (string Assembly, string Id)[] expected =
        [
            ("First.Owner.Tests", "PlannedTests.Executed"),
            ("Second.Owner.Tests", "OtherTests.Missing"),
            ("First.Owner.Tests", "PlannedTests.AlsoMissing"),
        ];

        var failure = Assert.Throws<InvalidDataException>(
            () => VerifyExpected(evidence, expected, expected));

        Assert.Equal(
            "TRX is missing protected-base planned test identities count=2 tests="
            + "First.Owner.Tests::PlannedTests.AlsoMissing | Second.Owner.Tests::OtherTests.Missing",
            failure.Message);
    }

    [Fact]
    public void AcceptsWhenEveryPlannedIdentityExecutedAlongsideAdditionalIdentities()
    {
        var evidence = new TestResultEvidence(
            4,
            new HashSet<(string Assembly, string Id)>
            {
                ("first.owner.tests", "TheoryTests.Parameterized"),
                ("Second.Owner.Tests", "FactTests.Required"),
                ("Candidate.New.Tests", "NewTests.Additional"),
            });
        (string Assembly, string Id)[] expected =
        [
            ("First.Owner.Tests", "TheoryTests.Parameterized"),
            ("Second.Owner.Tests", "FactTests.Required"),
        ];

        VerifyExpected(evidence, expected, expected);
    }

    [Fact]
    public void RejectsStaticSkipProtectedBaseIdentityThatStillExistsInCandidateSource()
    {
        const string skipReason = "candidate disabled a protected-base planned test";
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("First.Owner.Tests", "OtherTests.Executed"),
            },
            new Dictionary<(string Assembly, string Id), string>
            {
                [("First.Owner.Tests", "PlannedTests.Skipped")] = skipReason,
            });
        var expected = Planned("First.Owner.Tests", "PlannedTests.Skipped");
        var candidateSource = Candidate("First.Owner.Tests", "PlannedTests.Skipped");

        var failure = Assert.Throws<InvalidDataException>(
            () => VerifyExpected(evidence, [expected], [candidateSource]));

        Assert.Equal(
            "TRX is missing protected-base planned test identities count=1 tests="
            + "First.Owner.Tests::PlannedTests.Skipped",
            failure.Message);
    }

    [Fact]
    public void AcceptsDeletedProtectedBaseIdentityAndRecordsExemption()
    {
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("First.Owner.Tests", "OtherTests.Executed"),
            });
        var expected = Planned("Deleted.Owner.Tests", "DeletedTests.RemovedFact");
        using var output = new StringWriter { NewLine = "\n" };

        var executed = Program.VerifyExpectedTestEvidence(evidence, [expected], [], output);

        Assert.Equal(1, executed);
        Assert.Equal(
            "ENGINEERING_TEST_IDENTITY_EXEMPTED assembly=\"Deleted.Owner.Tests\" "
            + "id=\"DeletedTests.RemovedFact\" reason=candidate_source_absent\n",
            output.ToString());
    }

    [Fact]
    public void AcceptsRuntimeConditionalSkipAndRecordsDistinctExemption()
    {
        const string skipReason = "Live raw Lean report is absent; document graph verification requires that report.";
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("First.Owner.Tests", "OtherTests.Executed"),
            },
            new Dictionary<(string Assembly, string Id), string>
            {
                [("StrataLint.Scribe.Tests", "DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth")] = skipReason,
            });
        var expected = Planned(
            "StrataLint.Scribe.Tests",
            "DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth",
            skipReason);
        var candidateSource = Candidate(
            "StrataLint.Scribe.Tests",
            "DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth",
            skipReason);
        using var output = new StringWriter { NewLine = "\n" };

        var executed = Program.VerifyExpectedTestEvidence(
            evidence,
            [expected],
            [candidateSource],
            output);

        Assert.Equal(1, executed);
        Assert.Equal(
            "ENGINEERING_TEST_IDENTITY_EXEMPTED assembly=\"StrataLint.Scribe.Tests\" "
            + "id=\"DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth\" "
            + "reason=runtime_conditional_skip\n",
            output.ToString());
    }

    [Fact]
    public void RejectsStaticSkipEvenWhenItCopiesTheRuntimeConditionalMessage()
    {
        const string skipReason = "Live raw Lean report is absent; document graph verification requires that report.";
        var identity = (Assembly: "StrataLint.Scribe.Tests", Id: "DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth");
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("First.Owner.Tests", "OtherTests.Executed"),
            },
            new Dictionary<(string Assembly, string Id), string>
            {
                [identity] = skipReason,
            });
        var expected = Planned(identity.Assembly, identity.Id, skipReason);
        var candidateStaticSkip = Candidate(identity.Assembly, identity.Id);

        var failure = Assert.Throws<InvalidDataException>(
            () => VerifyExpected(evidence, [expected], [candidateStaticSkip]));

        Assert.Equal(
            "TRX is missing protected-base planned test identities count=1 tests="
            + "StrataLint.Scribe.Tests::DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth",
            failure.Message);
    }

    [Fact]
    public void RejectsRuntimeConditionalSkipWhenCandidateConditionContractChanged()
    {
        const string skipReason = "Live raw Lean report is absent; document graph verification requires that report.";
        var identity = (Assembly: "StrataLint.Scribe.Tests", Id: "DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth");
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)> { ("First.Owner.Tests", "OtherTests.Executed") },
            new Dictionary<(string Assembly, string Id), string> { [identity] = skipReason });
        var expected = new ExpectedTestIdentity(identity.Assembly, identity.Id, [skipReason], ["base-contract"]);
        var candidate = new CandidateTestIdentity(identity.Assembly, identity.Id, [skipReason], ["changed-contract"]);

        var failure = Assert.Throws<InvalidDataException>(
            () => VerifyExpected(evidence, [expected], [candidate]));

        Assert.Equal(
            "TRX is missing protected-base planned test identities count=1 tests="
            + "StrataLint.Scribe.Tests::DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth",
            failure.Message);
    }

    [Fact]
    public void RecordsDeletedIdentityBeforeRejectingIdentityStillInCandidateSource()
    {
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("First.Owner.Tests", "OtherTests.Executed"),
            });
        (string Assembly, string Id)[] expected =
        [
            ("Deleted.Owner.Tests", "DeletedTests.RemovedFact"),
            ("First.Owner.Tests", "PlannedTests.Skipped"),
        ];
        (string Assembly, string Id)[] candidateSource =
        [
            ("First.Owner.Tests", "PlannedTests.Skipped"),
        ];
        using var output = new StringWriter { NewLine = "\n" };

        var failure = Assert.Throws<InvalidDataException>(
            () => Program.VerifyExpectedTestEvidence(
                evidence,
                expected,
                candidateSource,
                output));

        Assert.Equal(
            "TRX is missing protected-base planned test identities count=1 tests="
            + "First.Owner.Tests::PlannedTests.Skipped",
            failure.Message);
        Assert.Equal(
            "ENGINEERING_TEST_IDENTITY_EXEMPTED assembly=\"Deleted.Owner.Tests\" "
            + "id=\"DeletedTests.RemovedFact\" reason=candidate_source_absent\n",
            output.ToString());
    }

    [Fact]
    public void RejectsRequiredAssemblyWithoutExecutedIdentity()
    {
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("Other.Owner.Tests", "ExecutedTest"),
            });

        var result = RunVerifyTrx(
            evidence,
            "--results-directory", "unused",
            "--required-assembly", "Missing.Owner.Tests");

        Assert.Equal(
            (
                ExitCode: 2,
                Output: "",
                Error: "TEST_EVIDENCE_FAILED TRX has no executed identity from required assembly Missing.Owner.Tests\n"),
            result);
    }

    [Fact]
    public void RejectsWhenAnyRequiredAssemblyLacksExecutedIdentity()
    {
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("Present.Owner.Tests", "ExecutedTest"),
            });

        var result = RunVerifyTrx(
            evidence,
            "--results-directory", "unused",
            "--required-assembly", "Present.Owner.Tests",
            "--required-assembly", "Missing.Owner.Tests");

        Assert.Equal(
            (
                ExitCode: 2,
                Output: "ENGINEERING_BASE_FLOOR_EXECUTED assembly=Present.Owner.Tests evidence=trx executed=1\n",
                Error: "TEST_EVIDENCE_FAILED TRX has no executed identity from required assembly Missing.Owner.Tests\n"),
            result);
    }

    [Fact]
    public void AcceptsWhenEveryRequiredAssemblyHasExecutedIdentity()
    {
        var evidence = new TestResultEvidence(
            2,
            new HashSet<(string Assembly, string Id)>
            {
                ("First.Owner.Tests", "FirstTest"),
                ("Second.Owner.Tests", "SecondTest"),
            });

        var result = RunVerifyTrx(
            evidence,
            "--results-directory", "unused",
            "--required-assembly", "First.Owner.Tests",
            "--required-assembly", "Second.Owner.Tests");

        Assert.Equal(
            (
                ExitCode: 0,
                Output: "ENGINEERING_BASE_FLOOR_EXECUTED assembly=First.Owner.Tests evidence=trx executed=1\n"
                    + "ENGINEERING_BASE_FLOOR_EXECUTED assembly=Second.Owner.Tests evidence=trx executed=1\n",
                Error: ""),
            result);
    }

    [Fact]
    public void UnknownVerifyTrxOptionFailsClosed()
    {
        var evidence = new TestResultEvidence(
            1,
            new HashSet<(string Assembly, string Id)>
            {
                ("Missing.Owner.Tests", "ExecutedTest"),
            });

        var result = RunVerifyTrx(
            evidence,
            "--results-directory", "unused",
            "--required-assmbly", "Missing.Owner.Tests");

        Assert.Equal(
            (
                ExitCode: 2,
                Output: "",
                Error: "TEST_EVIDENCE_FAILED unknown verify-trx option: --required-assmbly\n"),
            result);
    }

    private static (int ExitCode, string Output, string Error) RunVerifyTrx(
        TestResultEvidence evidence,
        params string[] options)
    {
        using var output = new StringWriter { NewLine = "\n" };
        using var error = new StringWriter { NewLine = "\n" };
        var exitCode = Program.Run(
            ["verify-trx", .. options],
            _ => evidence,
            output,
            error);
        return (exitCode, output.ToString(), error.ToString());
    }

    private static int VerifyExpected(
        TestResultEvidence evidence,
        IEnumerable<(string Assembly, string Id)> expected,
        IEnumerable<(string Assembly, string Id)> candidateSource)
    {
        using var output = new StringWriter { NewLine = "\n" };
        return Program.VerifyExpectedTestEvidence(evidence, expected, candidateSource, output);
    }

    private static int VerifyExpected(
        TestResultEvidence evidence,
        IEnumerable<ExpectedTestIdentity> expected,
        IEnumerable<CandidateTestIdentity> candidateSource)
    {
        using var output = new StringWriter { NewLine = "\n" };
        return Program.VerifyExpectedTestEvidence(evidence, expected, candidateSource, output);
    }

    private static ExpectedTestIdentity Planned(
        string assembly,
        string id,
        params string[] runtimeConditionalSkipReasons) => new(
            assembly,
            id,
            runtimeConditionalSkipReasons,
            runtimeConditionalSkipReasons.Length == 0 ? [] : ["protected-runtime-contract"]);

    private static CandidateTestIdentity Candidate(
        string assembly,
        string id,
        params string[] runtimeConditionalSkipReasons) => new(
            assembly,
            id,
            [.. runtimeConditionalSkipReasons],
            runtimeConditionalSkipReasons.Length == 0 ? [] : ["protected-runtime-contract"]);
}
