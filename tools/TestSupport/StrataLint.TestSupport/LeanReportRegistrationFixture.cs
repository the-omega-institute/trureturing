using System.Text.Json.Nodes;

namespace StrataLint.TestSupport;

// Authored synthetic registration shared by sparse report consumer fixtures.
// Its optional entries describe fixture variation, not production policy.
public static class LeanReportRegistrationFixture
{
    public const string ManifestPath = "lean-report-inputs.json";
    public const string LoaderPath = "tools/scripts/report/lean-report-selection.py";
    public const string Manifest = """
        {
          "config_inputs": {
            "exclude": [],
            "include": [
              {
                "optional": false,
                "pattern": "lean-toolchain"
              },
              {
                "optional": false,
                "pattern": "lake-manifest.json"
              },
              {
                "optional": false,
                "pattern": "lakefile.toml"
              },
              {
                "optional": true,
                "pattern": "lakefile.lean"
              }
            ]
          },
          "impact_cohorts": [
            {
              "depends_on": [
                "sources"
              ],
              "exclude": [],
              "id": "umbrella",
              "members": [
                "Trureturing.lean"
              ]
            },
            {
              "depends_on": [],
              "exclude": [],
              "id": "sources",
              "members": [
                "D5/**/*.lean"
              ]
            }
          ],
          "inspector_sources": {
            "exclude": [],
            "include": [
              {
                "optional": true,
                "pattern": "tools/lean-inspector/**/*.lean"
              }
            ]
          },
          "producer_scopes": {
            "lean-report": {
              "exclude": [
                "**/bin/**",
                "**/obj/**"
              ],
              "include": [
                {
                  "optional": false,
                  "pattern": "lean-report-inputs.json"
                },
                {
                  "optional": false,
                  "pattern": "tools/scripts/report/lean-report-selection.py"
                },
                {
                  "optional": false,
                  "pattern": "tools/scripts/worktree/lean-cache-publish.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Cli/**/*.cs"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Engine/**/*.cs"
                },
                {
                  "optional": true,
                  "pattern": "tools/Trureturing.Truth/**/*.cs"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Cli/StrataLint.Cli.csproj"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Engine/StrataLint.Engine.csproj"
                },
                {
                  "optional": true,
                  "pattern": "tools/Trureturing.Truth/Trureturing.Truth.csproj"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Cli/packages.lock.json"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Engine/packages.lock.json"
                },
                {
                  "optional": true,
                  "pattern": "tools/Trureturing.Truth/packages.lock.json"
                },
                {
                  "optional": true,
                  "pattern": "Directory.Build.props"
                },
                {
                  "optional": true,
                  "pattern": "Directory.Packages.props"
                },
                {
                  "optional": true,
                  "pattern": "Directory.Build.targets"
                },
                {
                  "optional": true,
                  "pattern": "global.json"
                },
                {
                  "optional": true,
                  "pattern": "tools/lean-inspector/inspect.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/lean-inspector/delta.py"
                },
                {
                  "optional": true,
                  "pattern": "tools/lean-inspector/materials.py"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/report/lean-report.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/report/lean-report-input.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/report/lean-report-cache.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/report/lean-report-cache.py"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/report/lean-report-ci-baseline.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/report/report-consumer.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/report/report-supervisor.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/lean-report-pair.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/worktree/lean-cache-input.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/worktree/lean-cache-ensure.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/worktree/lean-cache-run.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/lib/resource-observation-lib.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/workflow/install-lean-toolchain.sh"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/workflow/judge-content-address.sh"
                }
              ]
            },
            "scribe-content": {
              "exclude": [
                "**/bin/**",
                "**/obj/**"
              ],
              "include": [
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Scribe/**/*.cs"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Scribe.Documents/**/*.cs"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Scribe/StrataLint.Scribe.csproj"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Scribe/packages.lock.json"
                },
                {
                  "optional": true,
                  "pattern": "tools/StrataLint.Scribe.Documents/packages.lock.json"
                },
                {
                  "optional": true,
                  "pattern": "tools/scripts/workflow/scribe-content-checks.sh"
                },
                {
                  "optional": true,
                  "pattern": "Blueprint/**/*.scribe.cs"
                }
              ]
            }
          },
          "report_modules": {
            "exclude": [],
            "include": [
              {
                "optional": false,
                "pattern": "Trureturing.lean"
              },
              {
                "optional": true,
                "pattern": "D5/**/*.lean"
              }
            ]
          },
          "schema_version": 1
        }
        """;
    public const string LeanProjection = """
        {"config_inputs":{"exclude":[],"include":[{"optional":false,"pattern":"lean-toolchain"},{"optional":false,"pattern":"lake-manifest.json"},{"optional":false,"pattern":"lakefile.toml"},{"optional":true,"pattern":"lakefile.lean"}]},"impact_cohorts":[{"depends_on":["sources"],"exclude":[],"id":"umbrella","members":["Trureturing.lean"]},{"depends_on":[],"exclude":[],"id":"sources","members":["D5/**/*.lean"]}],"inspector_sources":{"exclude":[],"include":[{"optional":true,"pattern":"tools/lean-inspector/**/*.lean"}]},"producer_scopes":{"lean-report":{"exclude":["**/bin/**","**/obj/**"],"include":[{"optional":false,"pattern":"lean-report-inputs.json"},{"optional":false,"pattern":"tools/scripts/report/lean-report-selection.py"},{"optional":false,"pattern":"tools/scripts/worktree/lean-cache-publish.sh"},{"optional":true,"pattern":"tools/StrataLint.Cli/**/*.cs"},{"optional":true,"pattern":"tools/StrataLint.Engine/**/*.cs"},{"optional":true,"pattern":"tools/Trureturing.Truth/**/*.cs"},{"optional":true,"pattern":"tools/StrataLint.Cli/StrataLint.Cli.csproj"},{"optional":true,"pattern":"tools/StrataLint.Engine/StrataLint.Engine.csproj"},{"optional":true,"pattern":"tools/Trureturing.Truth/Trureturing.Truth.csproj"},{"optional":true,"pattern":"tools/StrataLint.Cli/packages.lock.json"},{"optional":true,"pattern":"tools/StrataLint.Engine/packages.lock.json"},{"optional":true,"pattern":"tools/Trureturing.Truth/packages.lock.json"},{"optional":true,"pattern":"Directory.Build.props"},{"optional":true,"pattern":"Directory.Packages.props"},{"optional":true,"pattern":"Directory.Build.targets"},{"optional":true,"pattern":"global.json"},{"optional":true,"pattern":"tools/lean-inspector/inspect.sh"},{"optional":true,"pattern":"tools/lean-inspector/delta.py"},{"optional":true,"pattern":"tools/lean-inspector/materials.py"},{"optional":true,"pattern":"tools/scripts/report/lean-report.sh"},{"optional":true,"pattern":"tools/scripts/report/lean-report-input.sh"},{"optional":true,"pattern":"tools/scripts/report/lean-report-cache.sh"},{"optional":true,"pattern":"tools/scripts/report/lean-report-cache.py"},{"optional":true,"pattern":"tools/scripts/report/lean-report-ci-baseline.sh"},{"optional":true,"pattern":"tools/scripts/report/report-consumer.sh"},{"optional":true,"pattern":"tools/scripts/report/report-supervisor.sh"},{"optional":true,"pattern":"tools/scripts/lean-report-pair.sh"},{"optional":true,"pattern":"tools/scripts/worktree/lean-cache-input.sh"},{"optional":true,"pattern":"tools/scripts/worktree/lean-cache-ensure.sh"},{"optional":true,"pattern":"tools/scripts/worktree/lean-cache-run.sh"},{"optional":true,"pattern":"tools/scripts/lib/resource-observation-lib.sh"},{"optional":true,"pattern":"tools/scripts/workflow/install-lean-toolchain.sh"},{"optional":true,"pattern":"tools/scripts/workflow/judge-content-address.sh"}]}},"report_modules":{"exclude":[],"include":[{"optional":false,"pattern":"Trureturing.lean"},{"optional":true,"pattern":"D5/**/*.lean"}]},"schema_version":1}
        """;

    public static void Install(string repository)
    {
        var loader = Path.Combine(repository, LoaderPath);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(loader)!);
        TemporaryFileSystem.File.WriteAllText(loader,
            System.IO.File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), LoaderPath)));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(repository, ManifestPath), Manifest + "\n");
    }

    public static void RegisterProducer(string repository, string relative, string scope = "lean-report")
    {
        var path = Path.Combine(repository, ManifestPath);
        var data = JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(path))!;
        data["producer_scopes"]![scope]!["include"]!.AsArray().Add(
            new JsonObject { ["pattern"] = relative, ["optional"] = false });
        TemporaryFileSystem.File.WriteAllText(path, data.ToJsonString());
    }
}
