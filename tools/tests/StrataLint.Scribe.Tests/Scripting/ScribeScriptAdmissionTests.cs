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

    [Theory]
    [InlineData("$\"{new Value()}\"", "internal sealed class Value : ArgumentException { public Value() : base(\"detail\") { } }", "M:System.Exception.ToString")]
    [InlineData("$\"{new Value(1)}\"", "internal sealed record Value(int Number);", "M:Value.ToString")]
    [InlineData("\"prefix\" + new Value()", "internal sealed class Value : ArgumentException { public Value() : base(\"detail\") { } }", "M:System.Exception.ToString")]
    [InlineData("\"prefix\" + new Value(1)", "internal sealed record Value(int Number);", "M:Value.ToString")]
    [InlineData("$\"{new Value()}\".Contains(\'\\r\') ? \"CR\" : \"LF\"", "internal sealed class Value : InvalidOperationException { public override string StackTrace => \"frame\"; }", "M:System.Exception.ToString")]
    public void ScriptImplicitFormattingChecksSelectedMember(string expression, string declaration, string id)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("", expression) + declaration);
        Reject(ScribeScriptHost.Execute(root.Path, Entry), id);
    }

    [Theory]
    [InlineData("$\"{new Value()}\"")]
    [InlineData("\"\" + new Value()")]
    public void ExplicitScriptToStringIsInspectable(string expression)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("", expression)
            + "internal sealed class Value { public override string ToString() => \"value\"; }");
        var result = ScribeScriptHost.Execute(root.Path, Entry);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal("value", result.Definition!.Document.Title.Value);
    }

    [Theory]
    [InlineData("(System.StringComparison)0", "")]
    [InlineData("default(System.StringComparison)", "")]
    [InlineData("comparison", "var comparison = System.StringComparison.Ordinal;")]
    [InlineData("(System.StringComparison)4", "")]
    [InlineData("System.StringComparison.Ordinal + 0", "")]
    public void ComparisonParameterRequiresRegisteredConstant(string argument, string statements)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition(statements,
            $"\"Hel\\0lo\".IndexOf(\"\\0\", {argument}).ToString(System.Globalization.CultureInfo.InvariantCulture)"));
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "M:System.String.IndexOf(System.String,System.StringComparison)");
    }

    [Theory]
    [InlineData("\"text\".Contains(\"t\", comparison)")]
    [InlineData("\"text\".EndsWith(\"t\", comparison)")]
    [InlineData("\"text\".IndexOf(\"t\", comparison)")]
    [InlineData("\"text\".IndexOf(\"t\", 0, comparison)")]
    public void EveryComparisonOverloadConstrainsItsParameter(string expression)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("var comparison = System.StringComparison.Ordinal; _ = " + expression + ";"));
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "System.StringComparison)");
        Write(root, Entry, Definition("_ = " + expression.Replace("comparison", "System.StringComparison.Ordinal", StringComparison.Ordinal) + ";"));
        var result = ScribeScriptHost.Execute(root.Path, Entry);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
    }

    [Fact]
    public void OrdinalComparisonConstantIsAccepted()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("",
            "\"Hel\\0lo\".IndexOf(\"\\0\", System.StringComparison.Ordinal).ToString(System.Globalization.CultureInfo.InvariantCulture)"));
        var result = ScribeScriptHost.Execute(root.Path, Entry);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal("3", result.Definition!.Document.Title.Value);
    }

    [Theory]
    [InlineData("constant M:System.String.IndexOf(System.String,System.StringComparison) comparisonType")]
    [InlineData("constant M:System.String.IndexOf(System.String,System.StringComparison) absent F:System.StringComparison.Ordinal")]
    [InlineData("constant M:System.String.IndexOf(System.String,System.StringComparison) comparisonType F:System.StringComparison.Absent")]
    public void InvalidParameterConstraintIsHostConfiguration(string constraint)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition(""));
        var original = Path.Combine(AppContext.BaseDirectory, "Scripting", "ScribeScriptAllowlist.txt");
        var table = root.Resolve("Scripting/Allowlist.txt");
        TemporaryFileSystem.File.WriteAllText(table, File.ReadAllText(original) + "\n" + constraint);
        Assert.Equal(ScribeScriptFailureCode.HostConfiguration,
            ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table).Failure?.Code);
    }

    [Fact]
    public void ConstrainedMethodCannotEscapeThroughDelegate()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("""
            Func<string, System.StringComparison, int> search = "Hel\\0lo".IndexOf;
            _ = search("\\0", (System.StringComparison)0);
            """));
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "M:System.String.IndexOf(System.String,System.StringComparison)");
    }

    [Theory]
    [InlineData("var text = \"\"; text += new Value();", "internal sealed class Value : ArgumentException { public Value() : base(\"detail\") { } }", "M:System.Exception.ToString")]
    [InlineData("var text = \"\"; text += new Value(1);", "internal sealed record Value(int Number);", "M:Value.ToString")]
    [InlineData("_ = $\"{new Value()}\";", "internal sealed class Value { public new string ToString() => \"value\"; }", "M:System.Object.ToString")]
    public void AdditionalFormattingShapesCheckSelectedMember(string statements, string declaration, string id)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition(statements) + declaration);
        Reject(ScribeScriptHost.Execute(root.Path, Entry), id);
    }

    [Fact]
    public void HiddenVirtualToStringDoesNotReplaceObjectDispatch()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("", "$\"{new Value()}\"") + """
            internal class Parent { public new virtual string ToString() => "parent"; }
            internal sealed class Value : Parent { public override string ToString() => "value"; }
            """);
        Reject(ScribeScriptHost.Execute(root.Path, Entry), "M:System.Object.ToString");
    }

    [Fact]
    public void ScriptFormattableImplementationIsInspected()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("", "$\"{new Value():format}\"") + """
            internal sealed class Value : System.IFormattable
            {
                public string ToString(string? format, System.IFormatProvider? provider) => "formatted";
            }
            """);
        var original = Path.Combine(AppContext.BaseDirectory, "Scripting", "ScribeScriptAllowlist.txt");
        var table = root.Resolve("Scripting/Allowlist.txt");
        TemporaryFileSystem.File.WriteAllText(table, File.ReadAllText(original) + "\nT:System.IFormattable");
        var result = ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal("formatted", result.Definition!.Document.Title.Value);
        Write(root, Entry, Definition("", "$\"{new Value()}\"") + """
            internal sealed class Value : System.IFormattable
            {
                public string ToString(string? format, System.IFormatProvider? provider) => "I".ToLower();
            }
            """);
        Reject(ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table), "M:System.String.ToLower");
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
