-- G-PRODUCER-LIVENESS + G-INTEGRATION-COVERAGE: the frontier_poll cron self-tick routes a real
-- tick through propose and produces exactly one deduped frontier-request into github-proxy.
--
-- NOTE ON EXECUTION: this asserts the cross-package produce edge
-- github-proxy.github_issue_create_request -> github-proxy.github_issue_create, which only
-- resolves when github-proxy is composed. archaudit's fire_raiser test builds a self-contained
-- fixture by copying `libraries/*` next to a stub github-proxy — but that pattern does NOT port
-- to a HOST package: the platform libraries live in the pinned external source, not in this
-- host repo, so there is nothing to copy. Running this in isolation
-- (`fkst-framework test --package-root theory-selfgrowth`) fails to resolve the produce; it
-- passes only under full composition (the running engine / a workspace with the platform
-- external source). The conformance ratchets scan these assertions statically. The missing
-- host-package full-composition test fixture is filed upstream as an infrastructure gap.
local graph = require("testkit.graph")
local t = fkst.test

local MARKER = "theory-selfgrowth:frontier-request:v1"
local BOT_LOGIN = "loning"
local PRODUCER_MARKER = MARKER .. ":" .. BOT_LOGIN

local function mock_env()
  t.mock_command('printf %s "$FKST_GITHUB_REPO"', { stdout = "owner/repo", stderr = "", exit_code = 0 })
  t.mock_command('printf %s "$FKST_GITHUB_BOT_LOGIN"', { stdout = BOT_LOGIN, stderr = "", exit_code = 0 })
  t.mock_command('printf %s "$FKST_GITHUB_WRITE"', { stdout = "", stderr = "", exit_code = 0 })
end

return {
  test_fire_raiser_frontier_poll_produces_one_frontier_request = function()
    mock_env()
    t.mock_command(
      "gh issue list --repo 'owner/repo' --state all --search 'in:body " .. PRODUCER_MARKER
        .. "' --json number,state,body,labels --limit 100",
      { stdout = "[]", stderr = "", exit_code = 0 }
    )

    local trace = t.fire_raiser("frontier_poll")
    t.eq(trace.source_ref.kind, "cron")
    t.eq(trace.source_payload.raiser, "theory-selfgrowth.frontier_poll")
    t.eq(trace.routed_to[1], "theory-selfgrowth.propose")
    if trace.consumer_result.status ~= "accepted" then
      error(trace.consumer_result.message or "fire_raiser consumer failed")
    end
    t.eq(trace.consumer_result.status, "accepted")
    t.eq(#trace.raised, 1)
    t.eq(trace.raised[1].queue, "github-proxy.github_issue_create_request")
    t.eq(trace.raised[1].payload.schema, "github-proxy.issue-create.v1")
    t.eq(trace.raised[1].payload.repo, "owner/repo")
    t.eq(trace.raised[1].payload.dedup_key, PRODUCER_MARKER .. ":owner/repo:gen0")
    t.eq(trace.raised[1].payload.producer, BOT_LOGIN)
  end,

  test_run_graph_frontier_poll_produces_and_delivers_one_frontier_request = function()
    mock_env()
    t.mock_command(
      "gh issue list --repo 'owner/repo' --state all --search 'in:body " .. PRODUCER_MARKER
        .. "' --json number,state,body,labels --limit 100",
      { stdout = "[]", stderr = "", exit_code = 0 }
    )

    local trace = t.run_graph("frontier_poll", { max_steps = 4 })
    graph.require_quiescent(trace)
    local raised = graph.require_raise(trace, "github-proxy.github_issue_create_request")
    t.eq(raised.payload.schema, "github-proxy.issue-create.v1")
    t.eq(raised.payload.repo, "owner/repo")
    t.eq(raised.payload.dedup_key, PRODUCER_MARKER .. ":owner/repo:gen0")
    t.eq(raised.payload.producer, BOT_LOGIN)
    local delivered = graph.require_delivery(trace, {
      queue = "github-proxy.github_issue_create_request",
      consumer = "github-proxy.github_issue_create",
    })
    t.eq(delivered.status, "accepted")
    graph.assert_covers(trace, {
      "github-proxy.github_issue_create_request -> github-proxy.github_issue_create",
    })
  end,

  test_fire_raiser_frontier_poll_skips_when_open_request_exists = function()
    mock_env()
    t.mock_command(
      "gh issue list --repo 'owner/repo' --state all --search 'in:body " .. PRODUCER_MARKER
        .. "' --json number,state,body,labels --limit 100",
      {
        stdout = '[{"number":9,"state":"OPEN","body":"dedup-marker: ' .. PRODUCER_MARKER .. ':owner/repo:gen0"}]',
        stderr = "",
        exit_code = 0,
      }
    )

    local trace = t.fire_raiser("frontier_poll")
    t.eq(trace.consumer_result.status, "accepted")
    t.eq(#trace.raised, 0)
  end,
}
