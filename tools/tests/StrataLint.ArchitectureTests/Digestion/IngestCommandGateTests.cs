using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

public sealed class IngestCommandGateTests
{
    [Fact]
    public void IngestRunRetainsBothReceiptIntegrityFailureGates()
    {
        var source = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools",
            "StrataLint.Cli",
            "Commands",
            "Digestion",
            "IngestCommand.cs"));
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        var run = Assert.Single(root.DescendantNodes().OfType<MethodDeclarationSyntax>(),
            static method => method.Identifier.ValueText == "Run");
        var gates = run.DescendantNodes()
            .OfType<InvocationExpressionSyntax>()
            .Where(static invocation =>
                InvocationName(invocation) == "RequireNoReceiptIntegrityFailure")
            .ToArray();

        Assert.Equal(
            ["derived", "evaluation"],
            gates.Select(static gate => gate.ArgumentList.Arguments[0].Expression.ToString()));

        var finalEvaluation = Assert.Single(run.DescendantNodes().OfType<VariableDeclaratorSyntax>(),
            static variable => variable.Identifier.ValueText == "evaluation");
        var backfillValidation = Assert.Single(run.DescendantNodes()
            .OfType<InvocationExpressionSyntax>(),
            static invocation => InvocationName(invocation) == "RequireValidBackfill");
        Assert.True(gates[1].SpanStart > finalEvaluation.Span.End);
        Assert.True(gates[1].Span.End < backfillValidation.SpanStart);

        AssertFlatTruthDerivations();
    }

    private static void AssertFlatTruthDerivations()
    {
        AssertTransaction(
            "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.cs",
            methodName: "Run",
            expectedEvaluations: 3);
        Assert.Empty(Calls(
            Method(
                "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.HostedExtension.cs",
                "RequireHostedExtension"),
            "LeanTruthStates.Resolve"));
        AssertTransaction(
            "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs",
            methodName: "Run",
            expectedEvaluations: 2);
        AssertTransaction(
            "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.AlignScribe.cs",
            methodName: "AlignScribeReceipt",
            expectedEvaluations: 2);

        var theoryCandidates = Method(
            "tools/StrataLint.Cli/Commands/TheoryGeneration/TheoryCandidatesCommand.cs",
            "Run");
        Assert.Single(Calls(theoryCandidates, "LeanTruthStates.Resolve"));
        AssertAllPassTruthStates(theoryCandidates, expectedEvaluations: 1);

        var prepare = Method(
            "tools/StrataLint.Cli/Commands/TruthExportCommand.cs",
            "PrepareStrictHistory");
        Assert.Single(Calls(prepare, "LeanTruthStates.Resolve"));
        Assert.Single(Calls(prepare, "LeanImportAdjacency.Build"));

        var completeCatalog = Method(
            "tools/StrataLint.Cli/Commands/Ledger/DagLedgerCommandPreparation.cs",
            "BuildCompleteCatalog");
        Assert.Empty(Calls(completeCatalog, "LeanTruthStates.Resolve"));
        Assert.Empty(Calls(completeCatalog, "LeanImportAdjacency.Build"));

        var release = Method(
            "tools/StrataLint.Cli/Commands/TruthReleaseCommand.cs",
            "Run");
        var projection = Assert.Single(Calls(release, "TruthDagProjectionAssembler.Build"));
        Assert.Equal(3, projection.ArgumentList.Arguments.Count);
        Assert.Equal(
            ["truth.Snapshot", "truth.Lean", "preparation.States"],
            projection.ArgumentList.Arguments.Select(static argument => argument.Expression.ToString()));
        var residual = Assert.Single(Calls(release, "ResidualFrontierAssembler.Assemble"));
        Assert.Equal(5, residual.ArgumentList.Arguments.Count);
        Assert.Equal(
            "preparation.States",
            residual.ArgumentList.Arguments[^1].Expression.ToString());
    }

    private static void AssertTransaction(
        string relativePath,
        string methodName,
        int expectedEvaluations)
    {
        var method = Method(relativePath, methodName);
        Assert.Single(Calls(method, "LeanTruthStates.Resolve"));
        AssertAllPassTruthStates(method, expectedEvaluations);
    }

    private static void AssertAllPassTruthStates(
        MethodDeclarationSyntax method,
        int expectedEvaluations)
    {
        var evaluations = Calls(method, "DigestionStatusEvaluator.Evaluate");
        Assert.Equal(expectedEvaluations, evaluations.Length);
        Assert.All(evaluations, static evaluation => Assert.Contains(
            evaluation.ArgumentList.Arguments,
            static argument => argument.NameColon?.Name.Identifier.ValueText == "truthStates"));
    }

    private static MethodDeclarationSyntax Method(string relativePath, string methodName)
    {
        var source = File.ReadAllText(Path.Combine(RepositoryLayout.FindRoot(), relativePath));
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        return Assert.Single(
            root.DescendantNodes().OfType<MethodDeclarationSyntax>(),
            method => method.Identifier.ValueText == methodName);
    }

    private static InvocationExpressionSyntax[] Calls(
        MethodDeclarationSyntax method,
        string expression) =>
        method.DescendantNodes()
            .OfType<InvocationExpressionSyntax>()
            .Where(invocation => string.Equals(
                invocation.Expression.ToString(),
                expression,
                StringComparison.Ordinal))
            .ToArray();

    private static string InvocationName(InvocationExpressionSyntax invocation) =>
        invocation.Expression switch
        {
            IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
            MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
            _ => string.Empty,
        };
}
