using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

public sealed class IngestCommandGateTests
{
    [Fact]
    public void IngestRunRetainsPostWriteRequireNoNewFailuresGate()
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
            .Where(static invocation => InvocationName(invocation) == "RequireNoNewFailures")
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
    }

    private static string InvocationName(InvocationExpressionSyntax invocation) =>
        invocation.Expression switch
        {
            IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
            MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
            _ => string.Empty,
        };
}
