using System.Xml.Linq;
using Microsoft.Build.Utilities;
using StrataLint.JudgeSeed;
using StrataLint.TestSupport;
using Xunit;

namespace JudgeSeedTask.Tests;

public sealed class JudgeSeedInputsTests : IDisposable
{
    private readonly string root = TemporaryFileSystem.Directory.CreateTempSubdirectory("judge-seed-inputs-").FullName;

    [Fact]
    public void CaptureIncludesCompilerFilesImportsAndAnalyzerCompanionsWithoutCompiling()
    {
        var task = Create();
        var source = Write("source with spaces.cs", "this is deliberately invalid C#");
        var reference = Write("reference.dll");
        var resource = Write("resource.bin");
        var additional = Write("additional.txt");
        var embedded = Write("embedded.cs");
        var manifest = Write("native.manifest");
        var analyzer = Write("analyzers/check.dll");
        var companion = Write("analyzers/implementation.dll");
        var unrelated = Write("analyzers/not-a-library.txt");
        var output = Path.Combine(root, "obj", "result.dll");
        var explicitInput = Write("explicit.input");
        task.Sources = [new TaskItem(source)];
        task.References = [new TaskItem(reference)];
        task.Resources = [new TaskItem(resource)];
        task.AdditionalFiles = [new TaskItem(additional)];
        task.EmbeddedFiles = [new TaskItem(embedded)];
        task.Win32Manifest = manifest;
        task.Analyzers = [new TaskItem(analyzer)];
        task.OutputAssembly = new TaskItem(output);
        task.JudgeInputs = [new TaskItem(explicitInput), new TaskItem(source), new TaskItem(output)];
        task.JudgeOutputs = [new TaskItem(output), new TaskItem(output)];

        var capture = Capture(task);

        Assert.Null(capture.Element("unsupported"));
        Assert.False(TemporaryFileSystem.File.Exists(output));
        var inputs = capture.Element("inputs")!.Elements("file").Select(file => file.Value).ToArray();
        foreach (var path in new[] { source, reference, resource, additional, embedded, manifest, analyzer,
                     companion, explicitInput, task.JudgeProject, Path.Combine(root, "settings.props"), typeof(object).Assembly.Location })
            Assert.Contains(path, inputs);
        Assert.DoesNotContain(output, inputs);
        Assert.DoesNotContain(unrelated, inputs);
        Assert.Equal(inputs.Distinct().Count(), inputs.Length);
        Assert.Equal(new[] { output }, capture.Element("outputs")!.Elements("file").Select(file => file.Value));
        Assert.Contains("\"" + source + "\"", capture.Element("arguments")!.Value, StringComparison.Ordinal);
        Assert.Equal(task.JudgeProject, capture.Attribute("project")!.Value);
        Assert.Equal(root, capture.Attribute("root")!.Value);
        Assert.Equal(task.JudgeIntermediate, capture.Attribute("obj")!.Value);
        Assert.Equal(task.JudgeOutput, capture.Attribute("bin")!.Value);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void GlobalPropertiesSelectConditionalImportsAndConfiguration(bool extra)
    {
        var task = Create();
        var engine = (CaptureBuildEngine)task.BuildEngine;
        engine.Properties["Flavor"] = extra ? "extra" : "plain";
        engine.Properties["Configuration"] = "Release";
        Write("extra.props", "<Project><PropertyGroup><RuntimeIdentifier>chosen-runtime</RuntimeIdentifier></PropertyGroup></Project>");
        Write("probe.csproj", """
            <Project>
              <Import Project="settings.props" />
              <Import Project="extra.props" Condition="'$(Flavor)' == 'extra'" />
              <PropertyGroup><Configuration>Debug</Configuration></PropertyGroup>
            </Project>
            """);

        var capture = Capture(task);

        Assert.Null(capture.Element("unsupported"));
        Assert.Equal(extra ? "test-sdk|net10.0|Release|AnyCPU|chosen-runtime" : "test-sdk|net10.0|Release|AnyCPU|",
            capture.Element("configuration")!.Value);
        Assert.Equal(extra, capture.Element("inputs")!.Elements("file").Any(file => file.Value == Path.Combine(root, "extra.props")));
    }

    [Fact]
    public void CompilerOptionsAndEnvironmentAreCapturedFromTheNativeCscTask()
    {
        var task = Create();
        task.Optimize = false;
        task.DefineConstants = "FIRST";
        task.EnvironmentVariables = ["CAPTURE_VALUE=first", "CAPTURE_OTHER=two"];
        var before = Capture(task);
        task.Optimize = true;
        task.DefineConstants = "SECOND";
        task.EnvironmentVariables = ["CAPTURE_VALUE=second"];

        var after = Capture(task);

        Assert.Null(before.Element("unsupported"));
        Assert.Null(after.Element("unsupported"));
        Assert.Contains("/optimize-", before.Element("arguments")!.Value, StringComparison.Ordinal);
        Assert.Contains("/define:FIRST", before.Element("arguments")!.Value, StringComparison.Ordinal);
        Assert.Contains("/optimize+", after.Element("arguments")!.Value, StringComparison.Ordinal);
        Assert.Contains("/define:SECOND", after.Element("arguments")!.Value, StringComparison.Ordinal);
        Assert.Equal("CAPTURE_VALUE=first\nCAPTURE_OTHER=two", before.Element("environment")!.Value);
        Assert.Equal("CAPTURE_VALUE=second", after.Element("environment")!.Value);
        Assert.NotEmpty(after.Element("runtime")!.Value);
    }

    [Theory]
    [InlineData("compiler", "custom compiler/response files/key container are not seedable")]
    [InlineData("key-container", "custom compiler/response files/key container are not seedable")]
    [InlineData("obj", "custom material directories are not seedable")]
    [InlineData("bin", "custom material directories are not seedable")]
    [InlineData("frameworks", "multiple target frameworks are not seedable")]
    public void UnsupportedInputsProduceARecordedFallback(string kind, string expected)
    {
        var task = Create();
        switch (kind)
        {
            case "compiler": task.JudgeCompilerOverrides = "custom-csc"; break;
            case "key-container": task.KeyContainer = "container"; break;
            case "obj": task.JudgeIntermediate = Path.Combine(root, "custom-obj"); break;
            case "bin": task.JudgeOutput = Path.Combine(root, "custom-bin"); break;
            case "frameworks": Write("probe.csproj", "<Project><PropertyGroup><TargetFrameworks>net9.0;net10.0</TargetFrameworks></PropertyGroup></Project>"); break;
        }

        var capture = Capture(task);

        Assert.Equal(expected, capture.Element("unsupported")!.Value);
        Assert.Null(capture.Element("inputs"));
        Assert.NotNull(capture.Element("outputs"));
    }

    [Fact]
    public void InvalidImportIsRecordedAsUnsupported()
    {
        var task = Create();
        Write("settings.props", "not an MSBuild project");

        var capture = Capture(task);

        Assert.Contains("settings.props", capture.Element("unsupported")!.Value, StringComparison.Ordinal);
        Assert.Null(capture.Element("inputs"));
    }

    [Fact]
    public void UnwritableCaptureDoesNotFailTheBuildOrClaimCapture()
    {
        var task = Create();
        var blocker = Write("blocked", "file blocks directory creation");
        task.JudgeCapture = Path.Combine(blocker, "capture.xml");

        Assert.True(task.Execute());

        Assert.False(task.JudgeCaptured);
        Assert.False(TemporaryFileSystem.File.Exists(task.JudgeCapture));
        Assert.Contains(((CaptureBuildEngine)task.BuildEngine).Messages,
            message => message.Message!.StartsWith("JUDGE_SEED capture unavailable: ", StringComparison.Ordinal));
    }

    private JudgeSeedInputs Create()
    {
        Write("settings.props", """
            <Project><PropertyGroup>
              <NETCoreSdkVersion>test-sdk</NETCoreSdkVersion><TargetFramework>net10.0</TargetFramework>
              <Configuration>Debug</Configuration><Platform>AnyCPU</Platform>
            </PropertyGroup></Project>
            """);
        return new JudgeSeedInputs
        {
            BuildEngine = new CaptureBuildEngine(),
            JudgeRoot = root,
            JudgeProject = Write("probe.csproj", "<Project><Import Project=\"settings.props\" /></Project>"),
            JudgeCapture = Path.Combine(root, "capture", "inputs.xml"),
            JudgeIntermediate = Path.Combine(root, "obj") + Path.DirectorySeparatorChar,
            JudgeOutput = Path.Combine(root, "bin") + Path.DirectorySeparatorChar,
        };
    }

    private static XElement Capture(JudgeSeedInputs task)
    {
        Assert.True(task.Execute());
        Assert.True(task.JudgeCaptured);
        return XElement.Parse(TemporaryFileSystem.File.ReadAllText(task.JudgeCapture));
    }

    private string Write(string relative, string text = "synthetic file input")
    {
        var path = Path.Combine(root, relative);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFileSystem.File.WriteAllText(path, text);
        return path;
    }

    public void Dispose() => TemporaryFileSystem.Directory.Delete(root, recursive: true);
}
