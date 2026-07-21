using System.Diagnostics;
using System.Text;

namespace StrataLint.Tests;

public sealed class TheorySelfgrowthTests
{
    [Fact]
    public void FrontierRequestDedupKeyIsScopedToIdleGeneration()
    {
        RunLua(
            """
            local core = require("core")

            local function idle_payload(detected_at)
              local expires_at = detected_at:gsub(":00:00Z$", ":10:00Z")
              return {
                schema = "idle-detector.system-idle.v1",
                detected_at = detected_at,
                expires_at = expires_at,
                source_ref = {
                  kind = "host-observe",
                  ref = "idle_tick/" .. detected_at,
                },
              }
            end

            local first = core.build_frontier_request("owner/repo", idle_payload("2026-07-20T01:00:00Z"))
            local replay = core.build_frontier_request("owner/repo", idle_payload("2026-07-20T01:00:00Z"))
            local next_generation = core.build_frontier_request("owner/repo", idle_payload("2026-07-20T02:00:00Z"))

            assert(first.dedup_key == replay.dedup_key, "same idle generation must replay with one dedup_key")
            assert(first.dedup_key ~= next_generation.dedup_key, "next idle generation must not be suppressed by a closed prior issue")
            assert(first.dedup_key ~= "theory-selfgrowth:frontier-request:v1:owner/repo", "repo-wide dedup_key would be lifetime dedup")
            assert(first.body:find("open-request-marker: theory-selfgrowth:frontier-request:v1", 1, true), "open marker must stay separate from generation dedup")
            assert(first.body:find("dedup-marker: " .. first.dedup_key, 1, true), "body must carry the generation dedup marker")
            """);
    }

    [Fact]
    public void ProposeRejectsExpiredIdleEventBeforeRaising()
    {
        RunLua(
            """
            local core = require("core")
            local raised = {}

            _G.exec_sync = function(_request)
              return { exit_code = 0, stdout = "owner/repo" }
            end
            _G.raise = function(queue, payload)
              table.insert(raised, { queue = queue, payload = payload })
            end
            _G.now = function()
              return core.iso_timestamp_epoch_seconds("2026-07-20T01:11:00Z")
            end

            require("departments.propose.main")

            local ok, err = pcall(pipeline, {
              queue = "idle-detector.system_idle",
              payload = {
                schema = "idle-detector.system-idle.v1",
                detected_at = "2026-07-20T01:00:00Z",
                expires_at = "2026-07-20T01:10:00Z",
                source_ref = { kind = "host-observe", ref = "idle_tick/2026-07-20T01:00:00Z" },
              },
            })

            assert(not ok, "expired idle event must fail closed")
            assert(tostring(err):find("expired", 1, true), "failure should name the expired idle hint")
            assert(#raised == 0, "expired idle event must not emit a GitHub request")
            """);
    }

    [Fact]
    public void ProposeRequiresProductionSystemIdleShape()
    {
        RunLua(
            """
            local core = require("core")
            local raised = {}

            _G.exec_sync = function(_request)
              return { exit_code = 0, stdout = "owner/repo" }
            end
            _G.raise = function(queue, payload)
              table.insert(raised, { queue = queue, payload = payload })
            end
            _G.now = function()
              return core.iso_timestamp_epoch_seconds("2026-07-20T01:05:00Z")
            end

            require("departments.propose.main")

            local ok, err = pcall(pipeline, {
              queue = "idle-detector.system_idle",
              payload = {
                schema = "idle-detector.system-idle.v2",
                detected_at = "2026-07-20T01:00:00Z",
                expires_at = "2026-07-20T01:10:00Z",
                source_ref = { kind = "host-observe", ref = "idle_tick/2026-07-20T01:00:00Z" },
              },
            })

            assert(not ok, "malformed idle event must fail closed")
            assert(tostring(err):find("invalid-system-idle", 1, true), "failure should name system_idle validation")
            assert(#raised == 0, "malformed idle event must not emit a GitHub request")
            """);
    }

    [Fact]
    public void ProposeEmitsGenerationScopedRequestForFreshIdleEvent()
    {
        RunLua(
            """
            local core = require("core")
            local raised = {}
            local exec_requests = {}

            _G.exec_sync = function(request)
              table.insert(exec_requests, request)
              if request.cmd:find("FKST_GITHUB_REPO", 1, true) then
                return { exit_code = 0, stdout = "owner/repo" }
              end
              if request.cmd:find("gh issue list", 1, true) then
                return { exit_code = 0, stdout = "0" }
              end
              return { exit_code = 1, stdout = "" }
            end
            _G.raise = function(queue, payload)
              table.insert(raised, { queue = queue, payload = payload })
            end
            _G.now = function()
              return core.iso_timestamp_epoch_seconds("2026-07-20T01:05:00Z")
            end

            require("departments.propose.main")
            pipeline({
              queue = "idle-detector.system_idle",
              payload = {
                schema = "idle-detector.system-idle.v1",
                detected_at = "2026-07-20T01:00:00Z",
                expires_at = "2026-07-20T01:10:00Z",
                source_ref = { kind = "host-observe", ref = "idle_tick/2026-07-20T01:00:00Z" },
              },
            })

            assert(#raised == 1, "fresh idle event should emit one request")
            assert(raised[1].queue == "github-proxy.github_issue_create_request")
            assert(raised[1].payload.dedup_key:find("2026-07-20T01:00:00Z", 1, true), "dedup_key must include the idle generation")
            assert(raised[1].payload.body:find("open-request-marker: theory-selfgrowth:frontier-request:v1", 1, true))
            assert(#exec_requests == 2, "fresh idle event should read repo and check open requests")
            assert(exec_requests[2].cmd:find("state:open", 1, true), "open-request exclusion must use an open-only query")
            assert(exec_requests[2].cmd:find("theory-selfgrowth:frontier-request:v1", 1, true), "open-request exclusion must search for the stable marker")
            """);
    }

    [Fact]
    public void ProposeSkipsWhenFrontierRequestIsAlreadyOpen()
    {
        RunLua(
            """
            local core = require("core")
            local raised = {}
            local exec_requests = {}

            _G.exec_sync = function(request)
              table.insert(exec_requests, request)
              if request.cmd:find("FKST_GITHUB_REPO", 1, true) then
                return { exit_code = 0, stdout = "owner/repo" }
              end
              if request.cmd:find("gh issue list", 1, true) then
                return { exit_code = 0, stdout = "1" }
              end
              return { exit_code = 1, stdout = "" }
            end
            _G.raise = function(queue, payload)
              table.insert(raised, { queue = queue, payload = payload })
            end
            _G.now = function()
              return core.iso_timestamp_epoch_seconds("2026-07-20T01:05:00Z")
            end

            require("departments.propose.main")
            pipeline({
              queue = "idle-detector.system_idle",
              payload = {
                schema = "idle-detector.system-idle.v1",
                detected_at = "2026-07-20T01:00:00Z",
                expires_at = "2026-07-20T01:10:00Z",
                source_ref = { kind = "host-observe", ref = "idle_tick/2026-07-20T01:00:00Z" },
              },
            })

            assert(#raised == 0, "existing open frontier request must suppress a new request")
            assert(#exec_requests == 2, "open-request exclusion must run before deciding to skip")
            assert(exec_requests[2].cmd:find("state:open", 1, true), "open-request exclusion must use an open-only query")
            assert(exec_requests[2].cmd:find("theory-selfgrowth:frontier-request:v1", 1, true), "open-request exclusion must search for the stable marker")
            """);
    }

    private static void RunLua(string script)
    {
        var root = FindRepositoryRoot();
        var packageRoot = Path.Combine(root, ".fkst", "local-packages", "theory-selfgrowth");
        var wrapped = LuaPrelude(packageRoot) + script;
        var scriptPath = Path.Combine(Path.GetTempPath(), "theory-selfgrowth-test-" + Guid.NewGuid().ToString("N") + ".lua");
        File.WriteAllText(scriptPath, wrapped, Encoding.UTF8);
        try
        {
            var start = new ProcessStartInfo
            {
                FileName = "lua",
                WorkingDirectory = root,
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
            };
            start.ArgumentList.Add(scriptPath);
            using var process = Process.Start(start) ?? throw new InvalidOperationException("could not start lua");
            var stdout = process.StandardOutput.ReadToEnd();
            var stderr = process.StandardError.ReadToEnd();
            Assert.True(process.WaitForExit(30_000), "lua test timed out");
            Assert.Equal(0, process.ExitCode);
            Assert.Equal("", stdout);
            Assert.Equal("", stderr);
        }
        finally
        {
            File.Delete(scriptPath);
        }
    }

    private static string LuaPrelude(string packageRoot) =>
        "local package_root = " + LuaQuote(packageRoot) + "\n"
        + "package.path = package_root .. '/?.lua;' .. package_root .. '/?/init.lua;' .. package_root .. '/departments/propose/?.lua;' .. package.path\n"
        + "package.preload['contract.strings'] = function()\n"
        + "  return { is_bounded_string = function(value, limit) return type(value) == 'string' and #value > 0 and #value <= limit end }\n"
        + "end\n";

    private static string LuaQuote(string value) =>
        "\"" + value.Replace("\\", "\\\\", StringComparison.Ordinal).Replace("\"", "\\\"", StringComparison.Ordinal) + "\"";

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
