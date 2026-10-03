namespace StrataLint.Scribe.Tests;

public sealed class ScribeScriptDispatchTests
{
    private const string Entry = "Blueprint/D5/S0/Test/Dispatch.scribe.cs";
    private const string Shared = "Blueprint/D5/S0/Test/Shared.scribe.cs";
    private const string Base = "internal record Base { public override string ToString() => \"base\"; }";
    private const string Derived = "internal record Derived : Base { public Derived() { } }";

    [Theory]
    [InlineData("_ = $\"{value}\";")]
    [InlineData("_ = \"prefix\" + value;")]
    [InlineData("var text = \"\"; text += value;")]
    [InlineData("_ = value.ToString();")]
    [InlineData("Func<string> format = value.ToString;")]
    [InlineData("var format = new Func<string>(value.ToString);")]
    public void BaseReferenceRejectsGeneratedDispatch(string statement)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("Base value = new Derived(); " + statement) + Base + Derived);
        Reject(root, "M:Derived.ToString");
    }

    [Theory]
    [InlineData("_ = $\"{value}\";")]
    [InlineData("_ = \"prefix\" + value;")]
    [InlineData("var text = \"\"; text += value;")]
    public void DerivedRecordWithExternalDataRejectsGeneratedDispatch(string statement)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("Base value = new Derived(); " + statement) + Base + """
            internal record Derived : Base
            {
                public Derived() { }
                public object Data => new ArgumentException("detail");
            }
            """);
        Reject(root, "M:Derived.ToString");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedTypesParticipateInDispatch(bool baseInShared)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, $"[ScribeSharedSource(\"{Shared}\")] "
            + Definition("Base value = new Derived(); _ = value.ToString();")
            + (baseInShared ? Derived : Base));
        Write(root, Shared, baseInShared ? Base : Derived);
        Reject(root, "M:Derived.ToString");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AbstractSlotChecksEveryImplementation(bool generated)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("Base value = new First(); _ = value.ToString();") + """
            internal abstract record Base { public abstract override string ToString(); }
            internal sealed record First : Base { public override string ToString() => "first"; }
            """ + (generated
                ? "internal sealed record Second : Base { }"
                : "internal sealed record Second : Base { public override string ToString() => \"second\"; }"));
        if (generated) Reject(root, "M:Second.ToString");
        else Accept(root);
    }

    [Theory]
    [InlineData("_ = value.ToString();")]
    [InlineData("_ = $\"{value}\";")]
    public void AbstractDerivedTypesRemainInTheClosedTypeEnumeration(string statement)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("Base value = new Derived(); " + statement) + """
            internal abstract record Base { public override string ToString() => "base"; }
            internal abstract record Middle : Base { }
            internal sealed record Derived : Middle { public override string ToString() => "derived"; }
            """);
        Reject(root, "M:Middle.ToString");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InterfaceSlotChecksEveryImplementation(bool generated)
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("IValue value = new First(); _ = value.ToString();") + """
            internal interface IValue { string ToString(); }
            internal sealed class First : IValue { public override string ToString() => "first"; }
            """ + (generated
                ? "internal sealed record Second : IValue { }"
                : "internal sealed class Second : IValue { public override string ToString() => \"second\"; }"));
        if (generated) Reject(root, "M:Second.ToString");
        else Accept(root);
    }

    [Fact]
    public void StaticInterfaceSlotRejectsGeneratedOperator()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("Value value = new Value(); _ = Operations.Equal(value, value);") + """
            internal interface IOps<T> where T : IOps<T>
            {
                static abstract bool operator ==(T left, T right);
                static abstract bool operator !=(T left, T right);
            }
            internal sealed record Value : IOps<Value>;
            internal static class Operations
            {
                public static bool Equal<T>(T left, T right) where T : IOps<T> => left == right;
            }
            """);
        Reject(root, "M:Value.op_Equality");
    }

    [Fact]
    public void EveryConstructedInterfaceImplementationIsChecked()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("IValue<string> value = new Value(); _ = value.ToString();") + """
            internal interface IValue<T> { string ToString(); }
            internal sealed record Value : IValue<int>, IValue<string>
            {
                string IValue<int>.ToString() => "value";
            }
            """);
        Reject(root, "M:Value.ToString");
    }

    [Fact]
    public void InterfacePropertyRejectsGeneratedAccessor()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("IValue value = new Value(1); _ = value.Number;") + """
            internal interface IValue { int Number { get; } }
            internal sealed record Value(int Number) : IValue;
            """);
        Reject(root, "M:Value.get_Number");
    }

    [Fact]
    public void InterfaceRejectsUnregisteredInheritedImplementation()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("IValue value = new Value(); _ = value.ToString();") + """
            internal interface IValue { string ToString(); }
            internal sealed class Value : ArgumentException, IValue { public Value() : base("detail") { } }
            """);
        Reject(root, "M:System.Exception.ToString");
    }

    [Fact]
    public void SourcePropertyOverridesAreInspectable()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("Base value = new First(); _ = value.Number;") + """
            internal abstract class Base { public abstract int Number { get; } }
            internal sealed class First : Base { public override int Number => 1; }
            internal sealed class Second : Base { public override int Number => 2; }
            """);
        Accept(root);
    }

    [Fact]
    public void UnformattedSealedRecordRemainsAccepted()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("var value = new Value(1); _ = value;")
            + "internal sealed record Value(int Number);");
        Accept(root);
    }

    [Fact]
    public void ExternalEqualityCallbackRejectsScriptElements()
    {
        using var root = new TemporaryRoot();
        Write(root, Entry, Definition("Value[] values = [new Value()]; _ = Array.IndexOf(values, values[0]);")
            + "internal sealed record Value;");
        Reject(root, "M:System.Array.IndexOf");
    }

    private static void Accept(TemporaryRoot root)
    {
        var result = ScribeScriptHost.Execute(root.Path, Entry);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
    }

    private static void Reject(TemporaryRoot root, string id) =>
        ScribeScriptAdmissionTests.Reject(ScribeScriptHost.Execute(root.Path, Entry), id);

    private static string Definition(string statements) => $$"""
        internal sealed class Probe : IScribeDocumentDefinition
        {
            public DocumentDefinition Create()
            {
                {{statements}}
                return DocumentDefinition.Create(ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text("content")))));
            }
        }
        """;

    private static void Write(TemporaryRoot root, string path, string body) =>
        TemporaryFileSystem.File.WriteAllText(root.Resolve(path),
            "using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl; " + body);
}
