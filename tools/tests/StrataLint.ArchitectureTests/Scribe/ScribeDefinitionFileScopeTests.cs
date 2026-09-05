namespace StrataLint.ArchitectureTests;

/// <summary>
/// 固化 τ=0 owner 2026-09-06 的设计裁决:**`.scribe.cs` 是独立脚本,不是互相引用的库**。
///
/// 全部 `Blueprint/**/*.scribe.cs` 被 `StrataLint.Scribe.Documents.csproj` 的
/// `&lt;Compile Include="../../Blueprint/**/*.scribe.cs" /&gt;` 编入同一程序集,
/// 但**那只是编译便利**:每个文件在语义上应当独立求值,如同一个脚本。
/// owner 原话:「就按 .scribe.cs 单文件算即可。实际上放在一个程序集也是为了编译方便,
/// 实际应该当脚本那么编译的。」
///
/// **为什么这条规则承重**:`describe-report --check` 若要按 changed paths 增量化,
/// 其正确性恰好依赖「改一个 `.scribe.cs` 不会改变另一个的内容」。PR #5625 曾因假定
/// 跨文件依赖存在而被判漏检(#5634),而实测存量为 **0**;本规则把「实测为 0」
/// 升级为「机器保证恒为 0」,从而使单文件增量成为**可依赖的**前提而非巧合。
///
/// **立条时的存量读数(2026-09-06)**:3165 个 `.scribe.cs`,每个恰好 1 个
/// `internal sealed class` + 1 个 `public DocumentDefinition Create`;
/// 引用 `StrataLint.Scribe.Blueprint` 命名空间下其他类型的行 **0**。
/// 故本规则是**纯增量门**(第 20 条「先立门后补账」:此处无账可补)。
/// </summary>
public sealed class ScribeDefinitionFileScopeTests
{
    private const string BlueprintNamespaceRoot = "StrataLint.Scribe.Blueprint";

    /// <summary>
    /// 一个 `.scribe.cs` 只允许在**自身的 namespace 声明**里出现 Blueprint 命名空间根。
    /// 任何其他出现都意味着它在引用另一个定义文件的类型 —— 即把脚本当成了库。
    /// </summary>
    internal static IReadOnlyList<string> InspectDefinitionSource(string relativePath, string source)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(relativePath);
        ArgumentNullException.ThrowIfNull(source);

        var findings = new List<string>();
        var lines = source.Split('\n');
        for (var index = 0; index < lines.Length; index++)
        {
            var line = lines[index].TrimEnd('\r');
            if (!line.Contains(BlueprintNamespaceRoot, StringComparison.Ordinal))
            {
                continue;
            }

            if (line.TrimStart().StartsWith("namespace ", StringComparison.Ordinal))
            {
                continue;
            }

            findings.Add($"{relativePath}:{index + 1}");
        }

        return findings;
    }

    [Fact]
    public void CrossDefinitionTypeReferenceIsRejected()
    {
        const string source = """
            namespace StrataLint.Scribe.Blueprint.D5.S0.Probe;

            internal sealed class ProbeDocument : IScribeDocumentDefinition
            {
                private const string Borrowed =
                    StrataLint.Scribe.Blueprint.D5.S0.Other.OtherDocument.Prefix;
            }
            """;

        var finding = Assert.Single(InspectDefinitionSource("Blueprint/D5/S0/Probe.scribe.cs", source));

        Assert.Equal("Blueprint/D5/S0/Probe.scribe.cs:6", finding);
    }

    // 放行侧:自身的 namespace 声明必须被接受,否则本规则会把每一个合法文件都判红。
    [Fact]
    public void OwnNamespaceDeclarationIsAccepted()
    {
        const string source = """
            namespace StrataLint.Scribe.Blueprint.D5.S0.Probe;

            internal sealed class ProbeDocument : IScribeDocumentDefinition
            {
                private const string Prefix = "D5/S0/Probe.";
            }
            """;

        Assert.Empty(InspectDefinitionSource("Blueprint/D5/S0/Probe.scribe.cs", source));
    }

    [Fact]
    public void EveryTrackedScribeDefinitionIsFileScoped()
    {
        var root = RepositoryLayout.FindRoot();
        var definitions = GitIndexRepositoryFiles
            .EnumerateDeclared(root, "Blueprint")
            .Where(static file => file.RelativePath.EndsWith(".scribe.cs", StringComparison.Ordinal))
            .ToArray();

        // 扫描面自证:前缀写错或 glob 失配会让本测试恒绿,故先钉住它确实选中了整个语料。
        Assert.True(
            definitions.Length > 3000,
            $"扫描面异常:只选中 {definitions.Length} 个 .scribe.cs,立条时实测为 3165 个");

        var violations = definitions
            .SelectMany(file => InspectDefinitionSource(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();

        Assert.Empty(violations);
    }
}
