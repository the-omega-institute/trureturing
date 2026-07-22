local M = {}

local strings = require("contract.strings")
local time = require("contract.time")

-- github-proxy.issue-create.v1 field bounds (mirror archaudit/core.lua limits).
local limits = {
  repo = 200,
  title = 240,
  body = 12000,
  dedup_key = 512,
  source_ref_kind = 80,
  source_ref_ref = 200,
}

-- Stable marker embedded in every frontier-request body. github-proxy routes this exact
-- title to `.fkst/workflows/frontier-generation.json`; the producer also searches its own
-- prior requests by this marker (see M.marker_search_query / M.decide_generation).
local REQUEST_MARKER = "theory-selfgrowth:frontier-request:v1"
-- GENERATE-NEW (2026-07-22): the prior title "Generate the next worthy D5 frontier obligation"
-- demanded a worth-argmax the substrate cannot compute (TruthNode has no worth/proposition/dep
-- fields), so the 5-judge intake correctly declined it (#359). This title instead asks the
-- consumer to PROPOSE-AND-PROVE a new theorem by mathematical judgment and routes on the
-- "Deliver ONE NEW D5 result:" prefix to blueprint-then-formalize (verified accepted + routed by
-- #366). Each self-tick's generation-scoped dedup key yields a distinct request; the consumer
-- picks a fresh (novelty-guarded) theorem each generation, so the library grows unbounded.
local REQUEST_TITLE = "Deliver ONE NEW D5 result: a new golden-integer theorem (proposer's choice)"

-- Reject idle hints older than this (mirror archaudit's 10-minute freshness budget): a
-- durable idle prompt must not create work once the system is no longer idle (#296 Major 2).
local FRESHNESS_BUDGET_SECONDS = 10 * 60

-- Self-tick poll interval (#346). theory-selfgrowth's ONLY trigger was `idle-detector.
-- system_idle`, which idle-detector broadcasts only when the bot has ZERO self-assigned open
-- issues (`idle_gate` self_assigned_open_issues==0) — effectively never, while any backlog is
-- open — so it has never fired once. (By contrast archaudit is also idle-gated, but on a
-- LOOSER signal — `is_idle_observe`, i.e. the durable observe is not truncated / queues are
-- not overflowing — AND it carries its own cron tick, so it fires on ordinary load; a host
-- package cannot reach that observe signal.) A periodic self-tick gives the frontier producer
-- a trigger it actually receives; the open-request exclusion (decide_generation) bounds output
-- to at most one open frontier-request at a time regardless of this interval, so it cannot flood.
local POLL_INTERVAL_SECONDS = 30 * 60

function M.request_marker() return REQUEST_MARKER end
function M.request_title() return REQUEST_TITLE end
function M.freshness_budget_seconds() return FRESHNESS_BUDGET_SECONDS end
function M.poll_interval() return POLL_INTERVAL_SECONDS end

-- Idempotency key handed to github-proxy — GENERATION-SCOPED (#296 Major 1).
-- github-proxy dedups by searching issues with `--state all` for the create-marker derived
-- from this key. A stable per-repo key matches the FIRST created issue forever (even after
-- it is closed), so the self-growth flywheel could only ever spin once. Scoping the key by
-- generation makes each new obligation's marker distinct, so `--state all` no longer matches
-- a prior CLOSED generation. The "at most one OPEN request at a time" invariant is enforced
-- SEPARATELY by the producer's open-request exclusion (see M.decide_generation) — hence
-- "idempotency scoped by generation, open-request exclusion done separately".
function M.dedup_key(repo, generation)
  return REQUEST_MARKER .. ":" .. tostring(repo) .. ":gen" .. tostring(generation)
end

-- Search query the producer runs against its OWN prior requests (used with
-- `gh issue list --state all --search <query>`) to compute the next generation and to
-- detect a still-open request. This is a READ for the dedup decision; issue-create egress
-- still stays with github-proxy.
function M.marker_search_query()
  return "in:body " .. REQUEST_MARKER
end

function M.validate_repo(repo)
  if type(repo) ~= "string" then return false end
  return repo:match("^[%w._-]+/[%w._-]+$") ~= nil
end

-- Decide the next generation index and whether an open request already exists, from the
-- producer's own frontier-request issues (each { state = ..., body = ... }). Issues are
-- filtered to those actually carrying REQUEST_MARKER in the body so an over-matching search
-- never inflates the counter.
--   generation  = count of prior requests (any state) -> index for the NEXT request
--   open_exists = any prior request still open        -> exclude firing (one at a time)
function M.decide_generation(issues)
  local generation = 0
  local open_exists = false
  if type(issues) == "table" then
    for _, issue in ipairs(issues) do
      if type(issue) == "table"
        and type(issue.body) == "string"
        and issue.body:find(REQUEST_MARKER, 1, true) ~= nil then
        generation = generation + 1
        local state = issue.state
        if state == "open" or state == "OPEN" then
          open_exists = true
        end
      end
    end
  end
  return { generation = generation, open_exists = open_exists }
end

-- Freshness verdict for a system_idle hint: "fresh" | "stale" | "expired" | "malformed".
-- Mirrors archaudit.core.idle_hint_freshness. "stale" when the hint's detected_at is older
-- than the budget; "expired" when its expires_at has already passed.
function M.idle_hint_freshness(detected_seconds, expires_seconds, now_seconds, budget_seconds)
  if type(detected_seconds) ~= "number"
    or type(now_seconds) ~= "number"
    or type(budget_seconds) ~= "number" then
    return "malformed"
  end
  if now_seconds - detected_seconds > budget_seconds then
    return "stale"
  end
  if expires_seconds ~= nil then
    if type(expires_seconds) ~= "number" then
      return "malformed"
    end
    if expires_seconds <= now_seconds then
      return "expired"
    end
  end
  return "fresh"
end

-- Assess a system_idle payload against the current clock (#296 Major 2). Validates the
-- schema tag and parses detected_at / optional expires_at via contract.time, then returns
-- the freshness verdict. Never trusts a durable idle hint blindly.
function M.assess_idle_payload(payload, now_seconds)
  if type(payload) ~= "table" then return "malformed" end
  if payload.schema ~= nil and payload.schema ~= "idle-detector.system-idle.v1" then
    return "malformed"
  end
  local detected = time.iso_timestamp_epoch_seconds(payload.detected_at)
  if detected == nil then return "malformed" end
  local expires = nil
  if payload.expires_at ~= nil then
    expires = time.iso_timestamp_epoch_seconds(payload.expires_at)
    if expires == nil then return "malformed" end
  end
  return M.idle_hint_freshness(detected, expires, now_seconds, FRESHNESS_BUDGET_SECONDS)
end

local function assert_field(ok, name)
  if not ok then
    error("theory-selfgrowth: invalid-request-field: " .. tostring(name), 0)
  end
end

local function body_text(dedup_key)
  return table.concat({
    "Theory self-growth (CLAUDE.md 第22条 open-driven flywheel): the system PROPOSES a new",
    "mathematical truth AND proves it, growing the library. Deliver as ONE conservative increment.",
    "",
    "Propose ONE genuinely-new, non-trivial, worthwhile theorem about the golden integers ℤ[φ]",
    "(`GoldenInt`), building ONLY on the already-CLOSED `D5/S0/Carrier/` library (Norm, Conj, Units,",
    "Euclidean/`EuclideanDomain GoldenInt`, GoldenRatio, Ring, AlgebraicModel — all proved sorry-free).",
    "Choose by mathematical judgment what is worthwhile and NOT already proven (美是罗盘, CLAUDE.md 第3条);",
    "do NOT compute or fabricate any novelty/worth number (the substrate cannot, and must not fake it).",
    "",
    "Deliver: a real Lean F-layer theorem (NOT a `Unit` placeholder), PROVED (`lake build` green;",
    "`#print axioms` shows NO `sorryAx` and NO custom/non-mathlib axiom), plus its mirroring Blueprint",
    "(B) narrative. Place it at the address + classification the repo's OWN rules dictate — derive the",
    "generality and target path from the classification + SL-003 capacity rules (a DERIVED consequence",
    "is typically `generality: I`); do NOT force a fixed path or mirror a base node's `generality: G`.",
    "",
    "Honesty guards: NON-VACUITY — reject trivial/vacuous statements (e.g. `P ∨ True`, `Nonempty`-of-",
    "trivial); pick a substantive claim. NOVELTY — search first; it must not already exist. CONSERVATIVE",
    "EXTENSION — append a new node only; never touch a frozen node.",
    "",
    "dedup-marker: " .. tostring(dedup_key),
  }, "\n")
end

-- Build the github-proxy.issue-create.v1 request that routes to blueprint-then-formalize
-- (propose-and-prove a new theorem). `generation` is the index from M.decide_generation; it
-- scopes the idempotency key so a fulfilled (closed) prior request no longer suppresses this one.
function M.build_frontier_request(repo, generation)
  assert_field(M.validate_repo(repo), "repo")
  local dedup_key = M.dedup_key(repo, generation)
  local title = REQUEST_TITLE
  local body = body_text(dedup_key)
  local source_ref_ref = tostring(repo) .. "#theory-selfgrowth#selfgrowth-deliver-intent"
  assert_field(strings.is_bounded_string(title, limits.title), "title")
  assert_field(strings.is_bounded_string(body, limits.body), "body")
  assert_field(strings.is_bounded_string(dedup_key, limits.dedup_key), "dedup_key")
  assert_field(strings.is_bounded_string(source_ref_ref, limits.source_ref_ref), "source_ref.ref")
  return {
    schema = "github-proxy.issue-create.v1",
    repo = tostring(repo),
    title = title,
    body = body,
    labels = {},
    dedup_key = dedup_key,
    source_ref = {
      kind = "repo-site",
      ref = source_ref_ref,
    },
  }
end

return M
