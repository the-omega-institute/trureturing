using System.Globalization;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeScriptAdmissionTests
{
    private const string Entry = "Blueprint/D5/S0/Test/Probe.scribe.cs";
    private const string Shared = "Blueprint/D5/S0/Test/Shared.scribe.cs";

    [Theory]
    [InlineData("\"scribe\".GetHashCode()", "M:System.String.GetHashCode")]
    [InlineData("new object().GetHashCode()", "M:System.Object.GetHashCode")]
    [InlineData("\"I\".ToLower()", "M:System.String.ToLower")]
    [InlineData("1.ToString()", "M:System.Int32.ToString")]
    [InlineData("\"scribe\".StartsWith(\"s\")", "M:System.String.StartsWith(System.String)")]
    public void ExternalMemberOverloadsAreRejected(string expression, string id)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition($"_ = {expression};"));
        Reject(ScribeScriptHost.Execute(root.Path, Entry), id);
    }

    [Theory]
    [InlineData("\"scribe\".GetHashCode()", "M:System.String.GetHashCode")]
    [InlineData("new object().GetHashCode()", "M:System.Object.GetHashCode")]
    [InlineData("\"I\".ToLower()", "M:System.String.ToLower")]
    [InlineData("1.ToString()", "M:System.Int32.ToString")]
    [InlineData("\"scribe\".StartsWith(\"s\")", "M:System.String.StartsWith(System.String)")]
    public void SharedExternalMemberOverloadsAreRejected(string expression, string id)
    {
        using var root = new TemporaryRoot();
        Write(root, Shared, $"internal static class Shared {{ internal static object Value => {expression}; }}");
        Write(root, Entry, $"[ScribeSharedSource(\"{Shared}\")] " + Definition("_ = Shared.Value;"));
        var result = ScribeScriptHost.Execute(root.Path, Entry);
        Reject(result, id);
        Assert.Equal(Shared, result.Failure!.RelativePath);
    }

    [Fact]
    public void ImplicitForeachMembersAreRejected()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("foreach (var value in new Values()) { _ = value; }")
            + "internal sealed class Values : List<int> { }");
        var table = TableWithout(root, "T:System.Collections.Generic.List`1.Enumerator");
        Reject(ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table), "T:System.Collections.Generic.List`1.Enumerator");
    }

    [Fact]
    public void ExternalImplicitFormattingIsRejected()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("_ = $\"{new object()}\";"));
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "T:System.Object");
    }

    [Fact]
    public void UserConversionCannotReachUnregisteredMembers()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("string value = new Value(); _ = value;")
            + "internal sealed class Value { public static implicit operator string(Value value) => \"I\".ToLower(); }");
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "M:System.String.ToLower");
    }

    [Fact]
    public void GeneratedMethodsWithoutInspectableBodiesAreRejected()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("_ = new Value(\"scribe\").GetHashCode();")
            + "internal sealed record Value(string Text);");
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "M:Value.GetHashCode");
    }

    [Fact]
    public void ImplicitBaseConstructorsRequireRegistration()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("").Replace("Probe : IScribeDocumentDefinition",
            "Probe : ArgumentException, IScribeDocumentDefinition", StringComparison.Ordinal));
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "M:System.ArgumentException.#ctor");
    }

    [Fact]
    public void UnhandledOperationKindsAreRejected()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("lock (new object()) { }"));
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "Lock");
    }

    [Fact]
    public void ExecutionFixesAndRestoresThreadCultures()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("", "$\"{1234:N0} {-5}\""));
        var culture = CultureInfo.CurrentCulture;
        var uiCulture = CultureInfo.CurrentUICulture;
        try
        {
            CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;
            CultureInfo.CurrentUICulture = CultureInfo.InvariantCulture;
            var expected = ScribeScriptHost.Execute(root.Path, Entry);
            Assert.True(expected.IsSuccess, expected.Failure?.ToString());
            var selected = (CultureInfo)new CultureInfo("tr-TR").Clone();
            selected.NumberFormat.NegativeSign = "~";
            CultureInfo.CurrentCulture = selected;
            CultureInfo.CurrentUICulture = selected;
            var actual = ScribeScriptHost.Execute(root.Path, Entry);
            Assert.True(actual.IsSuccess, actual.Failure?.ToString());
            Assert.Same(selected, CultureInfo.CurrentCulture);
            Assert.Same(selected, CultureInfo.CurrentUICulture);
            Assert.Equal(ScribeResourceCodec.Encode(expected.Definition!), ScribeResourceCodec.Encode(actual.Definition!));
        }
        finally
        {
            CultureInfo.CurrentCulture = culture;
            CultureInfo.CurrentUICulture = uiCulture;
        }
    }

    [Theory]
    [InlineData("all T:System.String")]
    [InlineData("all T:System.Collections.Generic.List`1")]
    [InlineData("M:System.String.StartsWith(System.String,System.Int32)")]
    [InlineData("M:System.String.StartsWith(System.Char)\nM:System.String.StartsWith(System.Char)")]
    [InlineData("T:System.Int32\nformat T:System.Int32\nformat T:System.Int32")]
    [InlineData("format T:System.Int32")]
    [InlineData("# types\n   ")]
    public void MemberTableConfigurationFailsClosed(string contents)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition(""));
        var table = root.Resolve("Scripting/Allowlist.txt");
        TemporaryFileSystem.File.WriteAllText(table, contents);
        var result = ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table);
        Assert.Equal(ScribeScriptFailureCode.HostConfiguration, result.Failure?.Code);
    }

    [Fact]
    public void RegisteredMemberCannotReturnAnUnregisteredType()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("_ = System.Globalization.CultureInfo.InvariantCulture;"));
        var table = TableWithout(root, "T:System.Globalization.CultureInfo");
        Reject(ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table), "T:System.Globalization.CultureInfo");
    }

    [Fact]
    public void ImplicitConversionMembersRequireRegistration()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("_ = \"value\"[1..2];"));
        var table = TableWithout(root, "M:System.Index.op_Implicit(System.Int32)~System.Index");
        Reject(ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table),
            "M:System.Index.op_Implicit(System.Int32)~System.Index");
    }

    [Theory]
    [InlineData("new System.Random()", "M:System.Random.#ctor")]
    [InlineData("\"prefix\" + new object()", "T:System.Object")]
    [InlineData("GidRef.Create(\"D5/S0/Test/Probe\").GetHashCode()", "M:StrataLint.Scribe.GidRef.GetHashCode")]
    public void UnregisteredStateAndFormattingMembersAreRejected(string expression, string id)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition($"_ = {expression};"));
        Reject(ScribeScriptHost.Execute(root.Path, Entry), id);
    }

    [Theory]
    [InlineData("unsafe { }", "unsafe")]
    [InlineData("int* pointer = null; _ = pointer;", "pointer")]
    [InlineData("extern", "extern")]
    public void UnsupportedExecutableSyntaxIsRejected(string statements, string reason)
    {
        using var root = new TemporaryRoot();
        var body = statements == "extern" ? Definition("") + "internal static class Native { public static extern void Invoke(); }"
            : Definition(statements);
        Write(root, Entry, body);
        Reject(ScribeScriptHost.Execute(root.Path, Entry), reason);
    }

    [Fact]
    public void RegisteredMembersSupportCompositeDefinitions()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("""
            IEnumerable<int> source = [1, 2];
            int[] values = [..source];
            List<int> copy = [..values];
            System.Collections.Immutable.ImmutableArray<int> immutable = [..copy];
            _ = immutable.Length;
            _ = "range"[1..];
            _ = "range"[..1];
            var sum = 0;
            foreach (var value in (IEnumerable<int>)values) sum += value;
            var pair = (Name: "sum", Total: values.Select(value => value + sum).ToArray()[0]);
            """, "$\"{pair.Name}:{pair.Total}\""));
        var result = ScribeScriptHost.Execute(root.Path, Entry);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal("sum:4", result.Definition!.Document.Title.Value);
    }

    private static string TableWithout(TemporaryRoot root, string id)
    {
        var original = Path.Combine(AppContext.BaseDirectory, "Scripting", "ScribeScriptAllowlist.txt");
        var table = root.Resolve("Scripting/Allowlist.txt");
        TemporaryFileSystem.File.WriteAllText(table, string.Join("\n", File.ReadAllLines(original).Where(line => line != id)));
        return table;
    }

    internal static void Reject(ScribeScriptResult result, string id)
    {
        Assert.True(result.Failure?.Code == ScribeScriptFailureCode.DisallowedSymbol, result.Failure?.ToString());
        Assert.True(result.Failure!.Message.Contains(id, StringComparison.Ordinal), result.Failure.ToString());
        Assert.Contains(result.Failure.RelativePath + ":", result.Failure.Message, StringComparison.Ordinal);
    }

    private static string Definition(string statements, string title = "\"title\"") => $$"""
        internal sealed class Probe : IScribeDocumentDefinition
        {
            public DocumentDefinition Create()
            {
                {{statements}}
                return DocumentDefinition.Create(ScribeNode.Create("digest", H({{title}}), Blocks(Paragraph(Text("content")))));
            }
        }
        """;

    private static void Write(TemporaryRoot root, string path, string body) =>
        TemporaryFileSystem.File.WriteAllText(root.Resolve(path),
            "using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl; " + body);
}
