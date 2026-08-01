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
local core = require("core")
local t = fkst.test

local MARKER = "theory-selfgrowth:frontier-request:v1"
local BOT_LOGIN = "loning"
local PRODUCER_MARKER = MARKER .. ":" .. BOT_LOGIN
local GH_COMMAND = "gh issue list --repo 'owner/repo' --state all --search 'in:body " .. PRODUCER_MARKER
  .. "' --json number,state,body,comments --limit 1000"
local DIGEST_COMMAND = core.formalize_candidates_command()
local CANDIDATES = [[{"schema":"stratalint-formalize-candidates-v2","ledger_sha256":"sha256:ledger","candidates":[{"source_id":"GICT","atom_id":"GICT-T0001","ast_path":"theorem/one","kind":"theorem","cas_ref":"sha256:cas1","raw_sha256":"sha256:raw1","atom_text":"Theorem one\nDerivation one"},{"source_id":"GICT","atom_id":"GICT-T0002","ast_path":"theorem/two","kind":"theorem","cas_ref":"sha256:cas2","raw_sha256":"sha256:raw2","atom_text":"Theorem two\nDerivation two"}],"withheld":[]}]]
local EMPTY_CANDIDATES = [[{"schema":"stratalint-formalize-candidates-v2","ledger_sha256":"sha256:ledger","candidates":[],"withheld":[]}]]

local function mock_env()
  t.mock_command('printf %s "$FKST_GITHUB_REPO"', { stdout = "owner/repo", stderr = "", exit_code = 0 })
  t.mock_command('printf %s "$FKST_GITHUB_BOT_LOGIN"', { stdout = BOT_LOGIN, stderr = "", exit_code = 0 })
  t.mock_command('printf %s "$FKST_GITHUB_WRITE"', { stdout = "", stderr = "", exit_code = 0 })
end

local function mock_history(stdout, exit_code)
  t.mock_command(GH_COMMAND, {
    stdout = stdout or "[]",
    stderr = "",
    exit_code = exit_code or 0,
  })
end

local function mock_candidates(stdout, exit_code)
  t.mock_command(DIGEST_COMMAND, {
    stdout = stdout or CANDIDATES,
    stderr = "",
    exit_code = exit_code or 0,
  })
end

return {
  test_fire_raiser_frontier_poll_produces_one_frontier_request = function()
    mock_env()
    mock_history()
    mock_candidates()

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
    t.eq(trace.raised[1].payload.dedup_key, "digestion-atom:GICT-T0001:sha256:cas1")
    t.eq(trace.raised[1].payload.producer, BOT_LOGIN)
    t.is_true(trace.raised[1].payload.body:find("atom_id: GICT-T0001", 1, true) ~= nil)
    t.is_true(trace.raised[1].payload.body:find("Theorem one\nDerivation one", 1, true) ~= nil)
  end,

  test_run_graph_frontier_poll_produces_and_delivers_one_frontier_request = function()
    mock_env()
    mock_history()
    mock_candidates()

    local trace = t.run_graph("frontier_poll", { max_steps = 4 })
    graph.require_quiescent(trace)
    local raised = graph.require_raise(trace, "github-proxy.github_issue_create_request")
    t.eq(raised.payload.schema, "github-proxy.issue-create.v1")
    t.eq(raised.payload.repo, "owner/repo")
    t.eq(raised.payload.dedup_key, "digestion-atom:GICT-T0001:sha256:cas1")
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
    mock_history('[{"number":9,"state":"OPEN","body":"frontier-request-marker: '
      .. PRODUCER_MARKER .. '\\ndedup-marker: digestion-atom:GICT-T0000:sha256:cas0"}]')

    local trace = t.fire_raiser("frontier_poll")
    t.eq(trace.consumer_result.status, "accepted")
    t.eq(#trace.raised, 0)
  end,

  test_fire_raiser_issue_500_terminal_marker_overrides_stale_thinking_label = function()
    mock_env()
    mock_history('[{"number":500,"state":"OPEN","body":"frontier-request-marker: '
      .. PRODUCER_MARKER .. '\\ndedup-marker: digestion-atom:GICT-T0000:sha256:cas0",'
      .. '"labels":[{"name":"fkst-dev:thinking"}],"comments":[{"body":"'
      .. '<!-- fkst:github-devloop:state:v1 proposal=\\"https://github.com/'
      .. 'the-omega-institute/trureturing/issues/500\\" state=\\"impl-failed\\" '
      .. 'attempt=\\"2\\" -->\\ngithub-devloop implementation failed: retry-exhausted"}]}]')
    mock_candidates()

    local trace = t.fire_raiser("frontier_poll")
    t.eq(trace.consumer_result.status, "accepted")
    t.eq(#trace.raised, 1)
  end,

  test_fire_raiser_frontier_poll_skips_empty_candidates = function()
    mock_env()
    mock_history()
    mock_candidates(EMPTY_CANDIDATES)
    local trace = t.fire_raiser("frontier_poll")
    t.eq(trace.consumer_result.status, "accepted")
    t.eq(#trace.raised, 0)
  end,

  test_fire_raiser_frontier_poll_skips_when_digest_command_fails = function()
    mock_env()
    mock_history()
    mock_candidates("", 1)
    local trace = t.fire_raiser("frontier_poll")
    t.eq(trace.consumer_result.status, "accepted")
    t.eq(#trace.raised, 0)
  end,

  test_fire_raiser_skips_attempted_candidate_and_round_robins = function()
    mock_env()
    mock_history('[{"number":8,"state":"CLOSED","body":"frontier-request-marker: '
      .. PRODUCER_MARKER .. '\\ndedup-marker: digestion-atom:GICT-T0002:sha256:cas2"}]')
    mock_candidates()
    local trace = t.fire_raiser("frontier_poll")
    t.eq(trace.consumer_result.status, "accepted")
    t.eq(#trace.raised, 1)
    t.eq(trace.raised[1].payload.dedup_key, "digestion-atom:GICT-T0001:sha256:cas1")
  end,

  test_fire_raiser_skips_oversize_candidate_without_truncating = function()
    mock_env()
    mock_history()
    mock_candidates('{"schema":"stratalint-formalize-candidates-v2","ledger_sha256":"sha256:ledger","candidates":['
      .. '{"source_id":"GICT","atom_id":"large","ast_path":"theorem/large","kind":"theorem","cas_ref":"sha256:large","raw_sha256":"sha256:raw-large","atom_text":"'
      .. string.rep("x", 12000) .. '"},'
      .. '{"source_id":"GICT","atom_id":"small","ast_path":"theorem/small","kind":"theorem","cas_ref":"sha256:small","raw_sha256":"sha256:raw-small","atom_text":"small theorem"}],"withheld":[]}')
    local trace = t.fire_raiser("frontier_poll")
    t.eq(trace.consumer_result.status, "accepted")
    t.eq(#trace.raised, 1)
    t.eq(trace.raised[1].payload.dedup_key, "digestion-atom:small:sha256:small")
    t.is_true(trace.raised[1].payload.body:find(string.rep("x", 12000), 1, true) == nil)
  end,
}
