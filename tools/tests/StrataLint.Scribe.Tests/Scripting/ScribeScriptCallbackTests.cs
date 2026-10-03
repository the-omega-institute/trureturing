namespace StrataLint.Scribe.Tests;

public sealed class ScribeScriptCallbackTests
{
    private const string Entry = "Blueprint/D5/S0/Test/Callback.scribe.cs";
    private const string IndexOf = "M:System.Array.IndexOf``1(``0[],``0)";
    private const string EnumerableMembers = """
        bool available = true;
        public IEnumerator<int> GetEnumerator() => this;
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => this;
        object System.Collections.IEnumerator.Current => 0;
        public bool MoveNext() { var result = available; available = false; return result; }
        public void Reset() { }
        public void Dispose() { }
        """;

    [Theory]
    [InlineData("_ = Enumerable.ToArray(new Values(7));")]
    [InlineData("")]
    public void DeclaredEnumerableRejectsGeneratedCurrent(string statements)
    {
        using var root = new TemporaryRoot();
        Write(root, Definition(statements) + """
            internal sealed record Values(int Current) : IEnumerable<int>, IEnumerator<int>
            {
            """ + EnumerableMembers + "}");
        Reject(root, "M:Values.get_Current");
    }

    [Fact]
    public void DeclaredEnumerableWithSourceMembersProducesDocument()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("var values = Enumerable.ToArray(new Values());", "$\"{values[0]}\"") + """
            internal sealed record Values : IEnumerable<int>, IEnumerator<int>
            {
                public int Current { get { return 7; } }
            """ + EnumerableMembers + "}");
        var result = ScribeScriptHost.Execute(root.Path, Entry);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal("7", result.Definition!.Document.Title.Value);
    }

    [Fact]
    public void DeclaredInterfaceRejectsAutoProperty()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("") + """
            internal sealed class Values : IEnumerator<int>
            {
                public int Current { get; } = 7;
                object System.Collections.IEnumerator.Current => 0;
                public bool MoveNext() => false;
                public void Reset() { }
                public void Dispose() { }
            }
            """);
        Reject(root, "M:Values.get_Current");
    }

    [Fact]
    public void DeclaredInterfaceChecksInheritedVirtualImplementations()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("") + """
            internal class Source : IEnumerator<int>
            {
                public virtual int Current { get { return 1; } }
                object System.Collections.IEnumerator.Current => 0;
                public bool MoveNext() => false;
                public void Reset() { }
                public void Dispose() { }
            }
            internal sealed class Values : Source { public override int Current { get; } = 7; }
            """);
        Reject(root, "M:Values.get_Current");
    }

    [Fact]
    public void DeclaredInterfaceRejectsUnregisteredInheritedMember()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("") + """
            internal sealed class Value : System.Globalization.CultureInfo, System.ICloneable
            {
                public Value() : base("") { }
            }
            """);
        var table = Table(root, "T:System.ICloneable\nM:System.Globalization.CultureInfo.#ctor(System.String)");
        ScribeScriptAdmissionTests.Reject(ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table),
            "M:System.Globalization.CultureInfo.Clone");
    }

    [Theory]
    [InlineData("nint value = 1; _ = value;", "T:System.IntPtr")]
    [InlineData("nuint value = 1; _ = value;", "T:System.UIntPtr")]
    [InlineData("_ = (nint)1;", "T:System.IntPtr")]
    [InlineData("_ = (nuint)1;", "T:System.UIntPtr")]
    [InlineData("_ = $\"{(nint)1}\";", "T:System.IntPtr")]
    [InlineData("_ = $\"{(nuint)1}\";", "T:System.UIntPtr")]
    public void NativeIntegerFormsAreRejected(string statements, string id)
    {
        using var root = new TemporaryRoot();
        Write(root, Definition(statements));
        Reject(root, id);
    }

    [Fact]
    public void NativeUnsignedShiftIsRejected()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("nuint number = (nuint)1 << 32;", "$\"{number}\""));
        Reject(root, "T:System.UIntPtr");
    }

    [Fact]
    public void NativeSignedOverflowBranchIsRejected()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("nint number = 2147483647; number = unchecked(number + 1);",
            "number < 0 ? \"32\" : \"64\""));
        Reject(root, "T:System.IntPtr");
    }

    [Fact]
    public void EqualityConstraintRejectsRecordElements()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("Value[] values = [new Value()]; _ = Array.IndexOf(values, values[0]);")
            + "internal sealed record Value;");
        Reject(root, IndexOf);
    }

    [Theory]
    [InlineData("_ = Array.IndexOf(new int[] { 1, 2 }, 2);")]
    [InlineData("_ = Array.IndexOf(new string[] { \"a\", \"b\" }, \"b\");")]
    public void EqualityConstraintAcceptsRegisteredElementTypes(string statements)
    {
        using var root = new TemporaryRoot();
        Write(root, Definition(statements));
        var result = ScribeScriptHost.Execute(root.Path, Entry);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
    }

    [Theory]
    [InlineData("type-argument M:System.Array.IndexOf``1(``0[],``0) T")]
    [InlineData("type-argument M:System.Array.IndexOf``1(``0[],``0) Missing T:System.Int32")]
    [InlineData("type-argument M:System.Array.Absent``1 T T:System.Int32")]
    [InlineData("type-argument M:System.Array.Empty``1 T T:System.Absent")]
    [InlineData("type-argument M:System.Array.Empty``1 T T:System.Int32,T:System.Int32")]
    [InlineData("type-argument M:System.Array.Empty``1 T T:System.Int32,")]
    [InlineData("type-argument M:System.Array.Empty``1  T T:System.Int32")]
    [InlineData("type-argument M:System.Array.Empty``1 T T:System.Int32\ntype-argument M:System.Array.Empty``1 T T:System.String")]
    [InlineData("type-argument M:System.Array.IndexOf``1(``0[],``0) T T:System.String")]
    [InlineData("type-argument M:System.Linq.Enumerable.Count``1(System.Collections.Generic.IEnumerable{``0}) TSource T:System.Int32")]
    public void InvalidTypeArgumentConstraintIsHostConfiguration(string constraint)
    {
        using var root = new TemporaryRoot();
        Write(root, Definition(""));
        var result = ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, Table(root, constraint));
        Assert.Equal(ScribeScriptFailureCode.HostConfiguration, result.Failure?.Code);
    }

    [Fact]
    public void TypeArgumentConstraintsApplyToOtherRegisteredMembers()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("_ = Array.Empty<int>();"));
        var table = Table(root, "type-argument M:System.Array.Empty``1 T T:System.String");
        ScribeScriptAdmissionTests.Reject(ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, Entry, table),
            "M:System.Array.Empty``1");
    }

    [Fact]
    public void TypeArgumentConstraintsApplyToMethodReferences()
    {
        using var root = new TemporaryRoot();
        Write(root, Definition("Func<Value[], Value, int> find = Array.IndexOf<Value>;")
            + "internal sealed record Value;");
        Reject(root, IndexOf);
    }

    [Theory]
    [InlineData("_ = sizeof(int);", "SizeOf")]
    [InlineData("_ = typeof(int);", "TypeOf")]
    public void ArchitectureObservationOperationsRemainDenied(string statements, string operation)
    {
        using var root = new TemporaryRoot();
        Write(root, Definition(statements));
        Reject(root, operation);
    }

    private static void Reject(TemporaryRoot root, string id) =>
        ScribeScriptAdmissionTests.Reject(ScribeScriptHost.Execute(root.Path, Entry), id);

    private static string Table(TemporaryRoot root, string appended)
    {
        var original = Path.Combine(AppContext.BaseDirectory, "Scripting", "ScribeScriptAllowlist.txt");
        var table = root.Resolve("Scripting/Allowlist.txt");
        TemporaryFileSystem.File.WriteAllText(table, File.ReadAllText(original) + "\n" + appended);
        return table;
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

    private static void Write(TemporaryRoot root, string body) =>
        TemporaryFileSystem.File.WriteAllText(root.Resolve(Entry),
            "using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl; " + body);
}
