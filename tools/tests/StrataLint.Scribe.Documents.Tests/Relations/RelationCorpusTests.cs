using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.Scribe.Documents.Tests;

public sealed class RelationCorpusTests(ITestOutputHelper output)
{
    [Fact]
    public void NarrowedPresentationMembersHaveNoCorpusInvocations()
    {
        var root = FindRoot();
        var counts = new SortedDictionary<string, int>(StringComparer.Ordinal)
        {
            ["System.Collections.Generic.List<T>.Clear"] = 0,
            ["System.Collections.Generic.List<T>.Remove"] = 0,
            ["System.Collections.Generic.List<T>.RemoveAt"] = 0,
            ["System.Linq.Enumerable.Prepend"] = 0,
            ["System.Linq.Enumerable.ToList"] = 0,
            ["System.Linq.Enumerable.Distinct"] = 0,
            ["System.Linq.Enumerable.OrderBy"] = 0,
            ["System.Linq.Enumerable.ThenBy"] = 0,
            ["System.String.Join"] = 0,
        };
        var names = counts.Keys.Select(key => key[(key.LastIndexOf('.') + 1)..]).ToHashSet(StringComparer.Ordinal);
        var references = ScribeScriptHost.ReferenceAssemblies();
        var options = ScribeScriptHost.ScriptParseOptions!;
        var candidates = 0;
        foreach (var path in Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories))
        {
            var syntax = CSharpSyntaxTree.ParseText(File.ReadAllText(path), options);
            if (!syntax.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>().Any(IsCandidate)) continue;
            var relative = Path.GetRelativePath(root, path).Replace('\\', '/');
            var graph = ScribeScriptHost.ReadSourceGraph(root, relative, options);
            Assert.Null(graph.Failure);
            var compilation = ScribeScriptHost.CreateSourceCompilation(root, graph.Sources!.Value, references, options);
            var tree = compilation.SyntaxTrees.Single(item => item.FilePath == relative);
            var model = compilation.GetSemanticModel(tree);
            foreach (var invocation in tree.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>().Where(IsCandidate))
            {
                var method = Assert.IsAssignableFrom<IMethodSymbol>(model.GetSymbolInfo(invocation).Symbol);
                candidates++;
                var type = method.ContainingType.SpecialType == SpecialType.System_String
                    ? "System.String" : method.ContainingType.OriginalDefinition.ToDisplayString();
                var key = type + "." + method.Name;
                if (counts.ContainsKey(key)) counts[key]++;
            }
        }
        output.WriteLine($"member invocation candidates={candidates}");
        foreach (var (member, count) in counts)
        {
            output.WriteLine($"member={member} invocations={count}");
            Assert.Equal(0, count);
        }

        bool IsCandidate(InvocationExpressionSyntax invocation) => invocation.Expression switch
        {
            MemberAccessExpressionSyntax member => names.Contains(member.Name.Identifier.ValueText),
            SimpleNameSyntax name => names.Contains(name.Identifier.ValueText),
            _ => false,
        };
    }

    [Fact]
    public void EveryStaticRelationProjectionMatchesExecution()
    {
        var root = FindRoot();
        var paths = Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).Order(StringComparer.Ordinal).ToArray();
        var result = RelationVerifier.Verify(root, paths);
        var text = new StringWriter();
        var error = new StringWriter();
        var exit = result.Write(text, error);
        output.WriteLine($"staticSeconds={result.StaticElapsed.TotalSeconds.ToString(System.Globalization.CultureInfo.InvariantCulture)}");
        foreach (var group in result.Items.Where(item => item.Unreadable is not null).GroupBy(item => item.Unreadable!.Shape).OrderBy(group => group.Key, StringComparer.Ordinal))
            output.WriteLine($"shape={group.Key} definitions={group.Count()}");
        output.WriteLine(text.ToString());
        output.WriteLine(error.ToString());
        Assert.Equal(0, result.HostFailures);
        Assert.Equal(0, result.Mismatches);
        var unreadable = result.Unreadable;
        Assert.Equal(unreadable == 0 ? 0 : 1, exit);
    }

    private static string FindRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory); directory is not null; directory = directory.Parent)
            if (File.Exists(Path.Combine(directory.FullName, "global.json"))
                && Directory.Exists(Path.Combine(directory.FullName, "Blueprint"))) return directory.FullName;
        throw new DirectoryNotFoundException("repository root was not found");
    }
}
