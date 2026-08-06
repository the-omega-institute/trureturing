-- Regression tests for the theory-selfgrowth digestion formalization producer.
-- Pure core-logic tests; the department's gh/exec IO is covered separately.

local core = require("core")
local time = require("contract.time")
local t = fkst.test

local MARKER = "theory-selfgrowth:frontier-request:v1"
local BOT_LOGIN = "loning"

-- A frontier-request issue as returned by `gh issue list --json state,body,comments`.
local function candidate(atom_id, atom_text, cas_ref)
  return {
    source_id = "GICT",
    atom_id = atom_id,
    ast_path = "theorem/example",
    kind = "theorem",
    cas_ref = cas_ref or ("sha256:cas-" .. atom_id),
    raw_sha256 = "sha256:raw-" .. atom_id,
    atom_text = atom_text or ("Theorem " .. atom_id .. "\nDerivation " .. atom_id),
  }
end

local function request_issue(_repo, generation, state, bot_login)
  local c = candidate("atom-" .. tostring(generation))
  return {
    state = state,
    body = table.concat({
      "frontier-request-marker: " .. core.producer_marker(bot_login or BOT_LOGIN),
      "dedup-marker: " .. core.atom_marker(c),
    }, "\n"),
  }
end

return {
  test_candidate_selection_is_fifo_with_generation_round_robin = function()
    local candidates = { candidate("a"), candidate("b"), candidate("c") }
    t.eq(core.select_candidate(candidates, 0, {}).atom_id, "a")
    t.eq(core.select_candidate(candidates, 1, {}).atom_id, "b")
    t.eq(core.select_candidate(candidates, 4, {}).atom_id, "b")
  end,

  test_candidate_selection_excludes_prior_atom_attempt_markers = function()
    local candidates = { candidate("a"), candidate("b"), candidate("c") }
    local prior = { { body = "dedup-marker: " .. core.atom_marker(candidates[2]) } }
    t.eq(core.select_candidate(candidates, 1, prior).atom_id, "c")
    t.eq(core.select_candidate({ candidates[2] }, 0, prior), nil)
  end,

  test_candidate_selection_prefers_kernel_volumes_foundation_first = function()
    local mk = function(id, source)
      return { source_id = source, atom_id = id, cas_ref = "sha256:cas-" .. id }
    end
    -- gict/observer higher-volume atoms are listed first, but the pzg/bedc kernel (内核卷)
    -- must be selected first: foundation-first (良基归纳), so a deep higher-volume theorem
    -- never stalls this one-at-a-time producer before its kernel prerequisites exist.
    local candidates = {
      mk("g1", "gict-v3.6"), mk("g2", "gict-v3.6"), mk("o1", "observer-quantum-v1"),
      mk("p1", "pzg-v170"), mk("b1", "bedc-wm-v0.1"),
    }
    for g = 0, 7 do
      local source = core.select_candidate(candidates, g, {}).source_id
      t.eq(source == "pzg-v170" or source == "bedc-wm-v0.1", true)
    end
  end,

  test_candidate_selection_falls_to_higher_volumes_when_kernel_exhausted = function()
    local mk = function(id, source)
      return { source_id = source, atom_id = id, cas_ref = "sha256:cas-" .. id }
    end
    -- No kernel atoms eligible -> higher-volume atoms become selectable (round-robin among them).
    local candidates = { mk("g1", "gict-v3.6"), mk("g2", "gict-v3.6") }
    t.eq(core.select_candidate(candidates, 0, {}).atom_id, "g1")
    t.eq(core.select_candidate(candidates, 1, {}).atom_id, "g2")
  end,

  test_atom_marker_and_request_dedup_are_atom_scoped = function()
    local c = candidate("GICT-T0042", nil, "sha256:abc123")
    local r = core.build_frontier_request("owner/repo", c, BOT_LOGIN)
    t.eq(core.atom_marker(c), "digestion-atom:GICT-T0042:sha256:abc123")
    t.eq(r.dedup_key, core.atom_marker(c))
    t.is_true(r.dedup_key:find(":gen", 1, true) == nil)
  end,

  test_build_frontier_request_embeds_atom_envelope_byte_exact = function()
    local text = "Theorem exact bytes\n  derivation: α + β\n"
    local c = candidate("GICT-T0042", text, "sha256:abc123")
    local r = core.build_frontier_request("owner/repo", c, BOT_LOGIN)
    t.eq(r.schema, "github-proxy.issue-create.v1")
    t.is_true(r.title:find("^Deliver ONE NEW D5 result:") ~= nil)
    t.is_true(r.title:find(c.atom_id, 1, true) ~= nil)
    t.is_true(r.title:find(c.cas_ref, 1, true) ~= nil)
    t.is_true(r.body:find("schema: theory%-selfgrowth%.formalize%-request%.v1") ~= nil)
    t.is_true(r.body:find("atom_id: " .. c.atom_id, 1, true) ~= nil)
    t.is_true(r.body:find("cas_ref: " .. c.cas_ref, 1, true) ~= nil)
    t.is_true(r.body:find("raw_sha256: " .. c.raw_sha256, 1, true) ~= nil)
    t.is_true(r.body:find(text, 1, true) ~= nil)
    t.is_true(r.body:find("exactly ONE new declaration-level Lean GID", 1, true) ~= nil)
    t.is_true(r.body:find("Blueprint mirror", 1, true) ~= nil)
    t.is_true(r.body:find(core.producer_marker(BOT_LOGIN), 1, true) ~= nil)
    t.eq(r.producer, BOT_LOGIN)
  end,

  test_build_frontier_request_requires_definition_closure_before_consensus = function()
    local r = core.build_frontier_request("owner/repo", candidate("GICT-T0042"), BOT_LOGIN)
    t.is_true(r.body:find("DEFINITION CLOSURE ADMISSION", 1, true) ~= nil)
    t.is_true(r.body:find("theory volume", 1, true) ~= nil)
    t.is_true(r.body:find("existing Lean corpus", 1, true) ~= nil)
    t.is_true(r.body:find("Mathlib standard concept", 1, true) ~= nil)
    t.is_true(r.body:find("definition-gap:", 1, true) ~= nil)
    t.is_true(r.body:find("skip this atom before consensus", 1, true) ~= nil)
    t.is_true(r.body:find("#710", 1, true) ~= nil)
  end,

  test_oversize_request_body_is_skipped_without_truncation = function()
    local c = candidate("large", string.rep("x", 12000))
    t.eq(core.build_frontier_request("owner/repo", c, BOT_LOGIN), nil)
  end,

  -- ---- Major 1: decide_generation (counter + open exclusion) ----
  test_decide_generation_empty_starts_at_zero = function()
    local d = core.decide_generation({}, BOT_LOGIN)
    t.eq(d.generation, 0)
    t.is_true(not d.open_exists)
  end,

  test_decide_generation_open_request_excludes_firing = function()
    local d = core.decide_generation({ request_issue("owner/repo", 0, "open") }, BOT_LOGIN)
    t.eq(d.generation, 1)
    t.is_true(d.open_exists)
  end,

  -- THE #373 REGRESSION: a terminal-blocked (fkst-dev:blocked) OPEN request must NOT freeze
  -- generation. A dropped/decomposed frontier-request is OPEN on GitHub until the ops cleanup
  -- closes it; counting it as "open" starved loning's producer for ~5h. The producer must
  -- self-recover and generate its next request while the terminal one is being cleaned up.
  test_terminal_blocked_open_request_does_not_freeze_generation = function()
    local blocked = request_issue("owner/repo", 0, "OPEN")
    blocked.comments = { {
      body = '<!-- fkst:github-devloop:state:v1 proposal="issue/373" state="blocked" -->',
    } }
    local d = core.decide_generation({ blocked }, BOT_LOGIN)
    t.eq(d.generation, 1)          -- still counted toward the generation index (monotonic)
    t.is_true(not d.open_exists)   -- but does NOT gate: producer self-recovers and fires gen1
  end,

  test_is_terminal_request_uses_authoritative_marker_not_labels = function()
    t.is_true(core.is_terminal_request({
      body = '<!-- fkst:github-devloop:state:v1 proposal="issue/373" state="blocked" -->',
    }))
    -- impl-failed is a devloop TERMINAL_STATE (retries exhausted); it must gate exactly like
    -- blocked so a request whose codex timed out does not freeze the producer forever (#446).
    t.is_true(core.is_terminal_request({ comments = { {
      body = '<!-- fkst:github-devloop:state:v1 proposal="issue/446" state="impl-failed" -->',
    } } }))
    t.is_true(core.is_terminal_request({
      labels = { { name = "fkst-dev:thinking" } },
      comments = { {
        body = '<!-- fkst:github-devloop:state:v1 proposal="issue/500" state="impl-failed" -->',
      } },
    }))
    t.is_true(not core.is_terminal_request({
      body = '<!-- fkst:github-devloop:state:v1 proposal="issue/501" state="implementing" -->',
    }))
    -- Labels are projections only: neither a stale active label nor a terminal-looking label
    -- can decide source-of-truth terminality.
    t.is_true(not core.is_terminal_request({ labels = { { name = "fkst-dev:implementing" } } }))
    t.is_true(not core.is_terminal_request({ labels = { { name = "fkst-dev:impl-failed" } } }))
    t.is_true(not core.is_terminal_request({}))
    t.is_true(not core.is_terminal_request("not-an-issue"))
  end,

  test_unsupported_authoritative_marker_version_fails_loudly = function()
    local ok, err = pcall(core.is_terminal_request, {
      comments = { {
        body = '<!-- fkst:github-devloop:state:v2 proposal="issue/502" state="impl-failed" -->',
      } },
    })
    t.is_true(not ok)
    t.is_true(tostring(err):find("unsupported-devloop-state-marker", 1, true) ~= nil)
  end,

  -- THE #446 REGRESSION: a terminal impl-failed (codex-timed-out, retry-exhausted) OPEN request
  -- must NOT freeze generation. A deep atom whose 3h codex budget is exceeded reaches impl-failed
  -- and its churn stops, but it stays OPEN on GitHub; counting it as open deadlocked the flywheel.
  test_impl_failed_open_request_does_not_freeze_generation = function()
    local failed = request_issue("owner/repo", 0, "OPEN")
    failed.labels = { { name = "fkst-dev:enabled" }, { name = "fkst-dev:impl-failed" } }
    failed.body = failed.body .. '\n<!-- fkst:github-devloop:state:v1 proposal="issue/446" '
      .. 'state="impl-failed" -->'
    local d = core.decide_generation({ failed }, BOT_LOGIN)
    t.eq(d.generation, 1)          -- still counted toward the generation index (monotonic)
    t.is_true(not d.open_exists)   -- but does NOT gate: producer self-recovers and fires gen1
  end,

  -- THE #500 REGRESSION: labels are a lagging projection. The authoritative append-only
  -- devloop marker says impl-failed, so the stale `thinking` label must not hold the slot.
  test_issue_500_stale_thinking_label_with_impl_failed_marker_does_not_freeze_generation = function()
    local failed = request_issue("owner/repo", 0, "OPEN")
    failed.labels = { { name = "fkst-dev:thinking" } }
    failed.comments = { {
      body = '<!-- fkst:github-devloop:state:v1 proposal="https://github.com/'
        .. 'the-omega-institute/trureturing/issues/500" state="impl-failed" attempt="2" -->\n'
        .. "github-devloop implementation failed: retry-exhausted",
    } }
    local d = core.decide_generation({ failed }, BOT_LOGIN)
    t.eq(d.generation, 1)
    t.is_true(not d.open_exists)
  end,

  -- Conservative: an ACTIVE (non-blocked) open request still gates, even with labels present.
  test_active_open_request_with_labels_still_freezes = function()
    local active = request_issue("owner/repo", 0, "OPEN")
    active.labels = { { name = "fkst-dev:enabled" }, { name = "fkst-dev:implementing" } }
    local d = core.decide_generation({ active }, BOT_LOGIN)
    t.is_true(d.open_exists)       -- an actively-in-progress request still means "one at a time"
  end,

  -- THE #296 REGRESSION: one request created then CLOSED -> next generation is producible.
  test_closed_then_next_generation = function()
    local d = core.decide_generation({ request_issue("owner/repo", 0, "closed") }, BOT_LOGIN)
    t.eq(d.generation, 1)
    t.is_true(not d.open_exists)   -- nothing open -> producer may fire again
  end,

  test_decide_generation_ignores_unrelated_issues = function()
    local d = core.decide_generation({
      { state = "open", body = "some unrelated issue" },
      request_issue("owner/repo", 0, "closed"),
    }, BOT_LOGIN)
    t.eq(d.generation, 1)          -- only the marker-bearing issue counts
    t.is_true(not d.open_exists)   -- the unrelated open issue does not gate us
  end,

  test_decide_generation_multiple_closed_advances_counter = function()
    local d = core.decide_generation({
      request_issue("owner/repo", 0, "closed"),
      request_issue("owner/repo", 1, "closed"),
    }, BOT_LOGIN)
    t.eq(d.generation, 2)
    t.is_true(not d.open_exists)
  end,

  test_producer_scoping_isolates_open_requests = function()
    local repo = "owner/repo"
    local loning_marker = core.producer_marker("loning")
    local elonsg_marker = core.producer_marker("elonsg")
    t.eq(loning_marker, MARKER .. ":loning")
    t.eq(elonsg_marker, MARKER .. ":elonsg")
    t.is_true(loning_marker ~= elonsg_marker)
    local loning_sees_only_elonsg_open = core.decide_generation({
      request_issue(repo, 0, "OPEN", "elonsg"),
    }, "loning")
    t.eq(loning_sees_only_elonsg_open.generation, 0)
    t.is_true(not loning_sees_only_elonsg_open.open_exists)

    local elonsg_sees_only_loning_open = core.decide_generation({
      request_issue(repo, 0, "OPEN", "loning"),
    }, "elonsg")
    t.eq(elonsg_sees_only_loning_open.generation, 0)
    t.is_true(not elonsg_sees_only_loning_open.open_exists)
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

  test_validate_bot_login = function()
    t.is_true(core.validate_bot_login("loning"))
    t.is_true(core.validate_bot_login("synthetic-bot"))
    t.is_true(core.validate_bot_login("AlyciaBHZ.bot_1"))
    t.is_true(not core.validate_bot_login(""))
    t.is_true(not core.validate_bot_login("bad/login"))
    t.is_true(not core.validate_bot_login(nil))
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
