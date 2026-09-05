using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

public sealed class DigestionStatusEvaluatorArchitectureTests
{
    [Fact]
    public void CompleteChainGapsUsesPrebuiltAtomIndex()
    {
        var source = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools",
            "StrataLint.Engine",
            "Digestion",
            "Evaluation",
            "DigestionStatusEvaluator.cs"));
        var root = CSharpSyntaxTree.ParseText(source).GetCompilationUnitRoot();
        var completeEvaluation = FindMethod(root, "CompleteEvaluation");
        var completeEvaluationBody = Assert.IsType<BlockSyntax>(completeEvaluation.Body);
        var completeChainGaps = FindMethod(root, "CompleteChainGaps");

        Assert.Collection(
            completeChainGaps.ParameterList.Parameters,
            static parameter =>
            {
                Assert.Equal("EntryWork", parameter.Type?.ToString());
                Assert.Equal("item", parameter.Identifier.ValueText);
            },
            static parameter =>
            {
                Assert.Equal("IReadOnlyDictionary<string, EntryWork>", parameter.Type?.ToString());
                Assert.Equal("byId", parameter.Identifier.ValueText);
            });
        Assert.DoesNotContain(
            completeChainGaps.DescendantNodes().OfType<InvocationExpressionSyntax>(),
            static invocation => InvocationName(invocation) == "ToDictionary");

        var indexBuild = Assert.Single(
            completeEvaluationBody.Statements.OfType<LocalDeclarationStatementSyntax>(),
            static statement => statement.Declaration.Variables.Any(static variable =>
                variable.Identifier.ValueText == "byId"
                && variable.Initializer?.Value is InvocationExpressionSyntax invocation
                && IsWorkIndexBuild(invocation)));
        var loop = Assert.Single(completeEvaluationBody.Statements.OfType<ForEachStatementSyntax>());
        Assert.True(
            completeEvaluationBody.Statements.IndexOf(indexBuild)
                < completeEvaluationBody.Statements.IndexOf(loop),
            "The chain-gap index must be built before CompleteEvaluation enters its item loop.");

        var completeChainGapsCall = Assert.Single(
            loop.DescendantNodes().OfType<InvocationExpressionSyntax>(),
            static invocation => InvocationName(invocation) == "CompleteChainGaps");
        Assert.Collection(
            completeChainGapsCall.ArgumentList.Arguments,
            static argument => Assert.Equal("item", argument.Expression.ToString()),
            static argument => Assert.Equal("byId", argument.Expression.ToString()));
    }

    private static MethodDeclarationSyntax FindMethod(
        CompilationUnitSyntax root,
        string methodName) =>
        Assert.Single(
            root.DescendantNodes().OfType<MethodDeclarationSyntax>(),
            method => method.Identifier.ValueText == methodName);

    private static bool IsWorkIndexBuild(InvocationExpressionSyntax invocation) =>
        invocation.Expression is MemberAccessExpressionSyntax
        {
            Expression: IdentifierNameSyntax { Identifier.ValueText: "work" },
            Name.Identifier.ValueText: "ToDictionary",
        }
        && invocation.ArgumentList.Arguments.Count == 2
        && invocation.ArgumentList.Arguments[0].Expression is SimpleLambdaExpressionSyntax
        {
            Parameter.Identifier.ValueText: "item",
            Body: MemberAccessExpressionSyntax keySelector,
        }
        && keySelector.ToString() == "item.Entry.AtomId"
        && invocation.ArgumentList.Arguments[1].Expression.ToString() == "StringComparer.Ordinal";

    private static string InvocationName(InvocationExpressionSyntax invocation) =>
        invocation.Expression switch
        {
            IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
            MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
            _ => string.Empty,
        };
}
