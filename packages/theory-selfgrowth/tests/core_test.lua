-- Regression tests for #296 (theory-selfgrowth self-growth flywheel).
-- Major 1: lifetime dedup -> generation-scoped dedup + open-request exclusion.
-- Major 2: idle-payload freshness (reject stale / expired durable idle hints).
-- Pure core-logic tests; the department's gh/exec IO is covered separately.

local core = require("core")
local time = require("contract.time")
local t = fkst.test

local MARKER = "theory-selfgrowth:frontier-request:v1"

-- A frontier-request issue as returned by `gh issue list --json state,body`. Its body
-- carries the generation-scoped dedup_key, which contains MARKER as a prefix.
local function request_issue(repo, generation, state)
  return { state = state, body = "dedup-marker: " .. core.dedup_key(repo, generation) }
end

return {
  -- ---- Major 1: generation-scoped dedup key ----
  test_dedup_key_is_generation_scoped = function()
    t.eq(core.dedup_key("owner/repo", 0), MARKER .. ":owner/repo:gen0")
    t.eq(core.dedup_key("owner/repo", 1), MARKER .. ":owner/repo:gen1")
    -- Distinct generations MUST produce distinct keys, else `--state all` dedup re-suppresses.
    t.is_true(core.dedup_key("owner/repo", 0) ~= core.dedup_key("owner/repo", 1))
  end,

  test_build_frontier_request_embeds_generation_key = function()
    local r = core.build_frontier_request("owner/repo", 2)
    t.eq(r.schema, "github-proxy.issue-create.v1")
    t.eq(r.title, core.request_title())
    t.eq(r.dedup_key, MARKER .. ":owner/repo:gen2")
    t.is_true(r.body:find(MARKER, 1, true) ~= nil)
  end,

  -- ---- Major 1: decide_generation (counter + open exclusion) ----
  test_decide_generation_empty_starts_at_zero = function()
    local d = core.decide_generation({})
    t.eq(d.generation, 0)
    t.is_true(not d.open_exists)
  end,

  test_decide_generation_open_request_excludes_firing = function()
    local d = core.decide_generation({ request_issue("owner/repo", 0, "open") })
    t.eq(d.generation, 1)
    t.is_true(d.open_exists)
  end,

  -- THE #296 REGRESSION: one request created then CLOSED -> next generation is producible.
  test_closed_then_next_generation = function()
    local d = core.decide_generation({ request_issue("owner/repo", 0, "closed") })
    t.eq(d.generation, 1)          -- next request is gen1, a DISTINCT dedup_key from gen0
    t.is_true(not d.open_exists)   -- nothing open -> producer may fire again
    -- The new key differs from the closed generation's, so github-proxy's --state all
    -- marker search no longer matches the closed issue.
    t.is_true(core.dedup_key("owner/repo", d.generation)
      ~= core.dedup_key("owner/repo", 0))
  end,

  test_decide_generation_ignores_unrelated_issues = function()
    local d = core.decide_generation({
      { state = "open", body = "some unrelated issue" },
      request_issue("owner/repo", 0, "closed"),
    })
    t.eq(d.generation, 1)          -- only the marker-bearing issue counts
    t.is_true(not d.open_exists)   -- the unrelated open issue does not gate us
  end,

  test_decide_generation_multiple_closed_advances_counter = function()
    local d = core.decide_generation({
      request_issue("owner/repo", 0, "closed"),
      request_issue("owner/repo", 1, "closed"),
    })
    t.eq(d.generation, 2)
    t.is_true(not d.open_exists)
  end,

  -- ---- Major 2: idle-hint freshness ----
  test_idle_freshness_fresh = function()
    t.eq(core.idle_hint_freshness(1000, nil, 1000, 600), "fresh")
    t.eq(core.idle_hint_freshness(1000, 2000, 1100, 600), "fresh")
  end,

  test_idle_freshness_stale = function()
    -- detected_at older than the budget window
    t.eq(core.idle_hint_freshness(1000, nil, 1000 + 601, 600), "stale")
  end,

  test_idle_freshness_expired = function()
    -- expires_at already passed
    t.eq(core.idle_hint_freshness(1000, 1500, 1500, 600), "expired")
    t.eq(core.idle_hint_freshness(1000, 1500, 1600, 600), "expired")
  end,

  test_assess_idle_payload_verdicts = function()
    local now = time.iso_timestamp_epoch_seconds("2026-07-22T12:00:00Z")
    -- fresh: detected just now, no expiry
    t.eq(core.assess_idle_payload(
      { schema = "idle-detector.system-idle.v1", detected_at = "2026-07-22T12:00:00Z" }, now), "fresh")
    -- stale: detected 20 min ago (budget 10 min)
    t.eq(core.assess_idle_payload(
      { schema = "idle-detector.system-idle.v1", detected_at = "2026-07-22T11:40:00Z" }, now), "stale")
    -- expired: expires in the past
    t.eq(core.assess_idle_payload(
      { detected_at = "2026-07-22T12:00:00Z", expires_at = "2026-07-22T11:59:00Z" }, now), "expired")
    -- malformed: bad schema / missing detected_at / bad timestamp
    t.eq(core.assess_idle_payload({ schema = "wrong", detected_at = "2026-07-22T12:00:00Z" }, now), "malformed")
    t.eq(core.assess_idle_payload({ detected_at = "not-a-time" }, now), "malformed")
    t.eq(core.assess_idle_payload("not a table", now), "malformed")
  end,

  test_validate_repo = function()
    t.is_true(core.validate_repo("owner/repo"))
    t.is_true(not core.validate_repo("owner"))
    t.is_true(not core.validate_repo(nil))
  end,

  -- ---- #346: self-tick raiser gives the frontier producer a real trigger ----
  test_poll_interval_is_a_duration_string = function()
    -- The raiser `interval` must be a duration STRING (the framework's parser rejects a bare
    -- integer). Guards the runtime regression where poll_interval returned 1800 (a number),
    -- which crashed raiser parsing at engine startup.
    local v = core.poll_interval()
    t.eq(type(v), "string")
    t.is_true(v:match("^%d+[smhd]$") ~= nil)
  end,

  test_frontier_raiser_is_a_cron_producing_the_tick = function()
    local raiser = require("raisers.frontier_poll")
    t.eq(raiser.type, "cron")
    t.eq(raiser.produces, "theory_selfgrowth_tick")
    t.eq(raiser.interval, core.poll_interval())
  end,
}
