using System.Text.Json.Nodes;

namespace StrataLint.TestSupport;

public static class RegPackageFixture
{
    // Pin/cache fixtures use the same independent package data as admission.
    public static void Write(string root)
    {
        var files = Files(File.ReadAllText(Path.Combine(root, "lake-manifest.json")));
        var reg = Path.Combine(root, "Reg");
        Directory.CreateDirectory(reg);
        foreach (var (path, text) in files)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, path))!);
            File.WriteAllText(Path.Combine(root, path), text);
        }
    }

    public static IReadOnlyDictionary<string, string> Files(string manifest)
    {
        var rootManifest = JsonNode.Parse(manifest)!;
        var packages = new JsonArray();
        foreach (var (name, directory, config) in new[]
                 {
                     ("trureturing", "..", "lakefile.toml"),
                     ("leanInspectorInterface", "../tools/lean-inspector-interface", "lakefile.toml"),
                     ("leanInspector", "../tools/lean-inspector", "lakefile.lean"),
                 })
            packages.Add(new JsonObject
            {
                ["type"] = "path", ["name"] = name, ["dir"] = directory,
                ["configFile"] = config, ["manifestFile"] = "lake-manifest.json", ["inherited"] = false,
            });
        foreach (var package in rootManifest["packages"]!.AsArray()
                     .Where(package => package!["type"]!.GetValue<string>() == "git"))
        {
            var inherited = package!.DeepClone();
            inherited["inherited"] = true;
            packages.Add(inherited);
        }
        var hostPackages = packages.DeepClone().AsArray();
        foreach (var package in hostPackages.Where(p => p!["type"]!.GetValue<string>() == "path"))
        {
            var name = package!["name"]!.GetValue<string>();
            package["dir"] = name switch
            {
                "trureturing" => "../..", "leanInspector" => "../lean-inspector",
                _ => "../lean-inspector-interface",
            };
            package["inherited"] = name != "leanInspector";
        }
        hostPackages.Insert(0, new JsonObject
        {
            ["type"] = "path", ["name"] = "reg", ["dir"] = "../../Reg",
            ["configFile"] = "lakefile.toml", ["manifestFile"] = "lake-manifest.json", ["inherited"] = false,
        });
        return new Dictionary<string, string>
        {
            ["tools/lean-inspector-reg/lakefile.toml"] = "name = \"regInspector\"\n",
            ["tools/lean-inspector-reg/lake-manifest.json"] = new JsonObject
            {
                ["version"] = "1.2.0", ["name"] = "regInspector",
                ["packagesDir"] = "../../.lake/packages", ["packages"] = hostPackages,
            }.ToJsonString() + "\n",
            ["Reg/lakefile.toml"] = """
            name = "reg"
            packagesDir = "../.lake/packages"
            buildDir = "../.lake/build/reg"
            defaultTargets = ["Reg"]
            [[require]]
            name = "trureturing"
            path = ".."
            [[require]]
            name = "leanInspectorInterface"
            path = "../tools/lean-inspector-interface"
            [[require]]
            name = "leanInspector"
            path = "../tools/lean-inspector"
            [[lean_lib]]
            name = "Reg"
            srcDir = ".."
            roots = ["Reg"]
            globs = ["Reg.+"]
            """ + "\n",
            ["Reg/lake-manifest.json"] = new JsonObject
            {
                ["version"] = "1.1.0", ["name"] = "reg",
                ["packagesDir"] = "../.lake/packages", ["packages"] = packages,
            }.ToJsonString() + "\n",
        };
    }
}
