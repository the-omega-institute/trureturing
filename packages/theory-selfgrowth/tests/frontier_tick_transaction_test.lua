local core = require("core")
local t = fkst.test

local repo_command = 'printf %s "$FKST_GITHUB_REPO"'
local search_command = "gh issue list --repo 'owner/repo' --state all --search '"
  .. core.marker_search_query()
  .. "' --json number,state,body --limit 100"

local function mock_reconciliation(existing_requests)
  t.mock_command(repo_command, {
    stdout = "owner/repo",
    stderr = "",
    exit_code = 0,
  })
  t.mock_command(search_command, {
    stdout = existing_requests or "[]",
    stderr = "",
    exit_code = 0,
  })
end

local function fire_tick()
  local trace = t.fire_raiser("frontier_poll")
  if trace.consumer_result.status ~= "accepted" then
    error(trace.consumer_result.message or "theory-selfgrowth tick consumer failed")
  end
  return trace
end

local function run_tick_delivery()
  local result = t.run_department("departments/propose/main.lua", {
    queue = "theory-selfgrowth.theory_selfgrowth_tick",
    payload = { raiser = "theory-selfgrowth.frontier_poll" },
  })
  if result.exit_code ~= 0 then
    error(result.error or "theory-selfgrowth tick delivery failed")
  end
  return result
end

return {
  test_tick_reconciles_semantic_frontier_demand_without_global_idle = function()
    mock_reconciliation("[]")

    local trace = fire_tick()

    t.eq(trace.source_ref.kind, "cron")
    t.eq(trace.source_payload.raiser, "theory-selfgrowth.frontier_poll")
    t.eq(trace.routed_to[1], "theory-selfgrowth.propose")
    t.eq(#trace.raised, 1)
    t.eq(trace.raised[1].queue, "github-proxy.github_issue_create_request")

    local request = trace.raised[1].payload
    t.eq(request.schema, "github-proxy.issue-create.v1")
    t.eq(request.repo, "owner/repo")
    t.eq(request.title, core.request_title())
    t.is_true(request.body:find("Periodic theory self-growth", 1, true) ~= nil)
    t.is_true(request.body:find("Idle-triggered", 1, true) == nil)
    t.is_true(request.body:find("TruthDagConstruction.DeriveState", 1, true) ~= nil)

    local calls = t.command_calls()
    t.eq(#calls, 2)
    t.eq(calls[1].rendered, repo_command)
    t.eq(calls[2].rendered, search_command)
  end,

  test_duplicate_tick_is_bounded_while_frontier_request_remains_open = function()
    local open_request = table.concat({
      '[{"number":7,"state":"OPEN","body":"dedup-marker: ',
      core.dedup_key("owner/repo", 0),
      '"}]',
    })
    mock_reconciliation("[]")
    mock_reconciliation(open_request)

    local first = run_tick_delivery()
    local duplicate = run_tick_delivery()

    t.eq(#first.raises, 1)
    t.eq(first.raises[1].payload.dedup_key, core.dedup_key("owner/repo", 0))
    t.eq(#duplicate.raises, 0)
  end,
}
