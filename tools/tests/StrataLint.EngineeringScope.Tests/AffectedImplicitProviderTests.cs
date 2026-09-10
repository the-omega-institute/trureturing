using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class AffectedImplicitProviderTests
{
    [Theory]
    [InlineData("framework")]
    [InlineData("increment")]
    [InlineData("decrement")]
    [InlineData("compound")]
    [InlineData("compound-conversion")]
    [InlineData("conversion")]
    [InlineData("deconstruction")]
    [InlineData("default-value")]
    [InlineData("record-value")]
    public void IndirectRuntimeInputsCannotReuseUnchangedCompiledSuccess(string form)
    {
        using var fixture = new AffectedExecutionFixture();
        fixture.Write("local-runtime/input.xml", "<value>pass</value>");
        var path = System.Text.Json.JsonSerializer.Serialize(Path.Combine(fixture.Root, "local-runtime/input.xml"));
        var read = "Xunit.Assert.True(System.IO.File.Exists(" + path + "));";
        var (body, members) = form switch
        {
            "framework" => ("Xunit.Assert.Equal(\"pass\", System.Xml.Linq.XDocument.Load(" + path + ").Root.Value);", ""),
            "increment" => ("var value = new Value(); value++;", "public static Value operator ++(Value value) { " + read + " return value; }"),
            "decrement" => ("var value = new Value(); value--;", "public static Value operator --(Value value) { " + read + " return value; }"),
            "compound" => ("var value = new Value(); value += 1;", "public static Value operator +(Value value, int add) { " + read + " return value; }"),
            "compound-conversion" => ("var value = new Value(); value += 1;", "public static int operator +(Value value, int add) => add; public static implicit operator Value(int value) { " + read + " return new Value(); }"),
            "conversion" => ("Value value = 1;", "public static implicit operator Value(int value) { " + read + " return new Value(); }"),
            "deconstruction" => ("var (first, second) = new Value();", "public void Deconstruct(out int first, out int second) { " + read + " first = second = 1; }"),
            "default-value" => ("Xunit.Assert.Equal(\"pass\", string.Join(' ', new Value[1]));", "public override string ToString() { " + read + " return \"pass\"; }"),
            "record-value" => ("Xunit.Assert.Equal(\"Value { pass }\", string.Join<Value>(' ', new[] { new Value() }));", "protected virtual bool PrintMembers(System.Text.StringBuilder builder) { " + read + " builder.Append(\"pass\"); return true; }"),
            _ => throw new ArgumentOutOfRangeException(nameof(form)),
        };
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", "using Xunit; namespace First; public class Tests { [Fact] public void Runs() { "
            + body + " } } public " + (form == "record-value" ? "record" : "struct") + " Value { " + members + " }");
        var build = fixture.Build();
        var cold = fixture.Tests(build);
        Assert.Equal(2, cold.Projects.Sum(project => project.Executed));
        var dll = Path.Combine(fixture.Root, "tools/tests/StrataLint.First/bin/Release/net10.0/StrataLint.First.dll");
        var identity = CommonExecutionEvidence.Hash(dll);
        // XDocument changes bytes without changing compiled inputs. Operators
        // lose a file they read indirectly through their compiler-bound target.
        if (form == "framework") fixture.Write("local-runtime/input.xml", "<value>fail</value>");
        else fixture.Remove("local-runtime/input.xml");
        var affected = fixture.Tests(build, expectedExit: null);
        var removed = form == "framework" ? RemoveAndRun() : affected;
        Assert.Equal(identity, CommonExecutionEvidence.Hash(dll));
        fixture.ClearSeed();
        var full = fixture.Tests(build, expectedExit: 1);
        Assert.NotNull(full.Projects[0].Error);
        Assert.NotNull(affected.Projects[0].Error);
        Assert.NotNull(removed.Projects[0].Error);
        Assert.DoesNotContain(affected.Projects[0].Coverage, row => row.Status == "reused");
        Assert.Equal(0, affected.Projects[1].Executed);
        Assert.Equal(affected.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
        Assert.NotEmpty(fixture.Plan().Actions[0].Unknown);

        TestExecutionRecord RemoveAndRun()
        {
            fixture.Remove("local-runtime/input.xml");
            return fixture.Tests(build, expectedExit: null);
        }
    }
}
