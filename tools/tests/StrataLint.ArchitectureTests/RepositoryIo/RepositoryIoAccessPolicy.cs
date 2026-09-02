using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

public sealed class RepositoryIoAccessPolicyTests
{
    [Fact]
    public void TemporaryFileSystemEveryPathBearingApiRoutesThroughEnsureTemporaryPath()
    {
        var source = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools",
            "TestSupport",
            "StrataLint.TestSupport",
            "TemporaryFileSystem.cs"));
        var syntax = CSharpSyntaxTree.ParseText(source).GetRoot();
        var temporaryFileSystem = syntax.DescendantNodes()
            .OfType<ClassDeclarationSyntax>()
            .Single(static type => type.Identifier.ValueText == "TemporaryFileSystem");
        var wrapperApis = temporaryFileSystem.Members
            .OfType<ClassDeclarationSyntax>()
            .SelectMany(static type => type.Members.OfType<MethodDeclarationSyntax>())
            .ToArray();

        Assert.NotEmpty(wrapperApis);
        foreach (var api in wrapperApis)
        {
            var operation = Assert.Single(
                api.DescendantNodes().OfType<InvocationExpressionSyntax>(),
                static invocation => invocation.Expression is MemberAccessExpressionSyntax member
                    && member.Expression.ToString() is "System.IO.File" or "System.IO.Directory");
            var operationName = ((MemberAccessExpressionSyntax)operation.Expression)
                .Name.Identifier.ValueText;
            if (operationName is "CreateTempSubdirectory" or "GetCurrentDirectory")
            {
                continue;
            }

            var guardedPath = Assert.IsType<InvocationExpressionSyntax>(
                operation.ArgumentList.Arguments[0].Expression);
            Assert.Equal("EnsureTemporaryPath", guardedPath.Expression.ToString());
            Assert.Equal(
                api.ParameterList.Parameters[0].Identifier.ValueText,
                Assert.Single(guardedPath.ArgumentList.Arguments).Expression.ToString());
        }
    }
}
