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

-- Stable base marker for frontier-request bodies. github-proxy routes this exact title to
-- `.fkst/workflows/frontier-generation.json`; the producer scopes this base by bot login
-- before embedding/searching it (see M.producer_marker / M.marker_search_query /
-- M.decide_generation), so each producer only sees its own prior requests.
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
-- a trigger it actually receives; the per-producer open-request exclusion (decide_generation)
-- bounds each bot to at most one open frontier-request regardless of this interval.
local POLL_INTERVAL_SECONDS = 30 * 60
-- The cron raiser's `interval` field must be a duration STRING (e.g. "30m"), not an integer —
-- the framework's raiser parser rejects a bare number ("invalid type: integer, expected a
-- string"). Mirror archaudit's audit_poll_interval, which is `tostring(minutes) .. "m"`.
local POLL_INTERVAL = tostring(math.floor(POLL_INTERVAL_SECONDS / 60)) .. "m"

function M.request_marker() return REQUEST_MARKER end
function M.request_title() return REQUEST_TITLE end
function M.freshness_budget_seconds() return FRESHNESS_BUDGET_SECONDS end
function M.poll_interval() return POLL_INTERVAL end

function M.validate_bot_login(bot_login)
  if type(bot_login) ~= "string" then return false end
  return bot_login:match("^[%w._-]+$") ~= nil
end

local function assert_bot_login(bot_login)
  if not M.validate_bot_login(bot_login) then
    error("theory-selfgrowth: malformed-bot-login: FKST_GITHUB_BOT_LOGIN is invalid: "
      .. tostring(bot_login), 0)
  end
end

function M.producer_marker(bot_login)
  assert_bot_login(bot_login)
  return REQUEST_MARKER .. ":" .. tostring(bot_login)
end

-- Idempotency key handed to github-proxy — GENERATION-SCOPED (#296 Major 1).
-- github-proxy dedups by searching issues with `--state all` for the create-marker derived
-- from this key. A stable per-repo key matches the FIRST created issue forever (even after
-- it is closed), so the self-growth flywheel could only ever spin once. Scoping the key by
-- producer + generation makes each bot's new obligation marker distinct, so `--state all`
-- no longer matches another producer or a prior CLOSED generation. The "at most one OPEN
-- request per producer at a time" invariant is enforced SEPARATELY by the producer's
-- open-request exclusion (see M.decide_generation) — hence "idempotency scoped by producer
-- and generation, open-request exclusion done separately".
function M.dedup_key(repo, generation, bot_login)
  return M.producer_marker(bot_login) .. ":" .. tostring(repo) .. ":gen" .. tostring(generation)
end

-- Search query the producer runs against its OWN prior requests (used with
-- `gh issue list --state all --search <query>`) to compute the next generation and to
-- detect a still-open request. This is a READ for the dedup decision; issue-create egress
-- still stays with github-proxy.
function M.marker_search_query(bot_login)
  return "in:body " .. M.producer_marker(bot_login)
end

function M.validate_repo(repo)
  if type(repo) ~= "string" then return false end
  return repo:match("^[%w._-]+/[%w._-]+$") ~= nil
end

-- github-devloop's append-only state marker is authoritative; `fkst-dev:*` labels are only a
-- fallible projection of it. The one-at-a-time gate therefore reads marker lineage from the
-- issue body/comments and never derives terminality from labels. This deliberately couples the
-- producer to the versioned v1 marker contract: a detectable version/shape change fails loudly
-- instead of silently restoring the stale-label deadlock seen on #373, #446, and #500.
local DEVLOOP_STATE_MARKER_VERSION = "v1"
local TERMINAL_DEVLOOP_STATES = {
  ["blocked"] = true,
  ["impl-failed"] = true,
  ["merged"] = true,
  ["declined"] = true,
}

local function latest_devloop_state_in_text(text, latest)
  if type(text) ~= "string" then
    return latest
  end

  local saw_marker = false
  for version in text:gmatch("fkst:github%-devloop:state:([^%s>]+)") do
    saw_marker = true
    if version ~= DEVLOOP_STATE_MARKER_VERSION then
      error("theory-selfgrowth: unsupported-devloop-state-marker: " .. tostring(version), 0)
    end
  end

  local parsed = false
  for attributes in text:gmatch(
    "<!%-%-%s*fkst:github%-devloop:state:v1%s+(.-)%s*%-%->") do
    local state = attributes:match('state%s*=%s*"([^"]+)"')
    if state == nil then
      error("theory-selfgrowth: malformed-devloop-state-marker: missing state", 0)
    end
    latest = state
    parsed = true
  end
  if saw_marker and not parsed then
    error("theory-selfgrowth: malformed-devloop-state-marker: expected v1 HTML comment", 0)
  end
  return latest
end

function M.authoritative_devloop_state(issue)
  if type(issue) ~= "table" then return nil end
  local latest = latest_devloop_state_in_text(issue.body, nil)
  if type(issue.comments) == "table" then
    for _, comment in ipairs(issue.comments) do
      if type(comment) == "table" then
        latest = latest_devloop_state_in_text(comment.body, latest)
      end
    end
  end
  return latest
end

function M.is_terminal_request(issue)
  return TERMINAL_DEVLOOP_STATES[M.authoritative_devloop_state(issue)] == true
end

-- Decide the next generation index and whether an open request already exists, from the
-- producer's own frontier-request issues (each { state = ..., body = ..., comments = ... }).
-- Issues are filtered to those actually carrying the producer-scoped marker in the body so an
-- over-matching search never inflates the counter or lets another bot suppress this one.
--   generation  = count of prior requests (any state) -> index for the NEXT request
--   open_exists = any prior request still open without authoritative terminal state -> exclude
--                 firing (one ACTIVE at a time; terminal requests do not freeze generation)
function M.decide_generation(issues, bot_login)
  local producer_marker = M.producer_marker(bot_login)
  local generation = 0
  local open_exists = false
  if type(issues) == "table" then
    for _, issue in ipairs(issues) do
      if type(issue) == "table"
        and type(issue.body) == "string"
        and issue.body:find(producer_marker, 1, true) ~= nil then
        generation = generation + 1
        local state = issue.state
        if (state == "open" or state == "OPEN") and not M.is_terminal_request(issue) then
          open_exists = true
        end
      end
    end
  end
  return { generation = generation, open_exists = open_exists }
end

-- Atom-scoped dedup marker for a digestion formalize-candidate. Stable provenance keyed to the
-- immutable atom identity (atom_id + cas_ref), NOT generation: a per-atom request is deduped by
-- which atom it targets. The ledger (not GitHub history) decides residual membership; this marker
-- only prevents re-firing the same atom while a prior attempt is still around.
function M.atom_marker(candidate)
  return "digestion-atom:" .. tostring(candidate.atom_id) .. ":" .. tostring(candidate.cas_ref)
end

-- Shell command that invokes slice 1's read-only candidate projection. Single source of truth
-- so the producer and its graph test never drift. Runs the canonical StrataLint CLI from the
-- deployment checkout root ($FKST_HOST_ROOT) -- `StrataLint` is not a bare command on PATH, so
-- mirror the Makefile invocation (`dotnet run --project ...`); `--verbosity quiet` keeps build
-- chatter off stdout so the JSON parses, and cd $FKST_HOST_ROOT lets RepositoryLayout.FindRoot
-- locate BACKFILL.yaml + the CAS atoms. On a cold build this can take ~1-2 min, so the caller
-- allows a generous timeout; a failed/absent command fails closed to a no-op.
function M.formalize_candidates_command()
  return 'cd "$FKST_HOST_ROOT" && dotnet run --project '
    .. 'Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release '
    .. '--verbosity quiet -- digest-status --formalize-candidates'
end

-- Select one candidate from the (already ordinal-sorted) digestion formalize-candidates
-- projection. Candidates whose atom_marker already appears in a prior request body are excluded
-- (per-atom attempt dedup). Among the remaining, a generation-indexed round-robin picks one
-- deterministically -- fair coverage, NOT easy-first (no fabricated difficulty/worth). Returns
-- nil on an empty eligible set (honest no-op).
-- `is_admissible` (optional) is an extra per-candidate eligibility predicate (e.g. "its request
-- body fits the issue limit"); a candidate failing it is skipped this round exactly like an
-- already-attempted one, so the round-robin lands on the next admissible candidate rather than
-- no-op'ing on an oversize pick.
function M.select_candidate(candidates, generation, prior_issues, is_admissible)
  if type(candidates) ~= "table" then
    return nil
  end
  local eligible = {}
  for _, candidate in ipairs(candidates) do
    local marker = M.atom_marker(candidate)
    local attempted = false
    if type(prior_issues) == "table" then
      for _, issue in ipairs(prior_issues) do
        if type(issue) == "table"
          and type(issue.body) == "string"
          and issue.body:find(marker, 1, true) ~= nil then
          attempted = true
          break
        end
      end
    end
    if not attempted and (is_admissible == nil or is_admissible(candidate)) then
      eligible[#eligible + 1] = candidate
    end
  end
  local n = #eligible
  if n == 0 then
    return nil
  end
  -- Foundation-first (良基归纳; CLAUDE.md 第〇节 well-founded induction + 第22条 frontier):
  -- the PZG/BEDC kernel volumes (内核卷) underpin the GICT/observer-quantum higher volumes, so
  -- formalize kernel atoms before higher-volume ones. This is DEPENDENCY order, not fabricated
  -- easy-first: a deep higher-volume theorem whose kernel prerequisites are not yet formalized
  -- deadlocks on undefined prerequisites (observed: GICT theorems 6.14/6.17 stall at consensus
  -- round 0, never terminalizing and freezing this one-at-a-time producer). Round-robin still
  -- gives fair coverage WITHIN the kernel stratum; higher volumes are reached once the kernel
  -- eligible set is exhausted (attempted atoms drop out per the per-atom dedup above).
  local kernel = {}
  for _, candidate in ipairs(eligible) do
    local source = tostring(candidate.source_id)
    if source:sub(1, 4) == "pzg-" or source:sub(1, 5) == "bedc-" then
      kernel[#kernel + 1] = candidate
    end
  end
  local pool = (#kernel > 0) and kernel or eligible
  return pool[((tonumber(generation) or 0) % #pool) + 1]
end

-- Build the github-proxy issue-create request for a digestion formalize target. The routing title
-- keeps the "Deliver ONE NEW D5 result:" prefix (github-proxy routes it to blueprint-then-
-- formalize) and names the atom; the body carries a versioned envelope with the byte-exact theory
-- statement + derivation and both markers (producer-scoped for generation counting, atom-scoped
-- for per-atom dedup). dedup_key is atom-scoped (never :gen). Returns nil when the rendered body
-- would exceed the github-proxy body limit -- the candidate is skipped this round, never truncated.
function M.build_frontier_request(repo, candidate, bot_login)
  local producer_marker = M.producer_marker(bot_login)
  local atom_marker = M.atom_marker(candidate)
  local title = "Deliver ONE NEW D5 result: formalize "
    .. tostring(candidate.atom_id) .. " (" .. tostring(candidate.cas_ref) .. ")"
  local body = table.concat({
    "schema: theory-selfgrowth.formalize-request.v1",
    "frontier-request-marker: " .. producer_marker,
    "dedup-marker: " .. atom_marker,
    "atom_id: " .. tostring(candidate.atom_id),
    "source_id: " .. tostring(candidate.source_id),
    "ast_path: " .. tostring(candidate.ast_path),
    "kind: " .. tostring(candidate.kind),
    "cas_ref: " .. tostring(candidate.cas_ref),
    "raw_sha256: " .. tostring(candidate.raw_sha256),
    "",
    "Formalize exactly ONE new declaration-level Lean GID faithful to the full theory claim "
      .. "below, with its Blueprint mirror; use the derivation as the proof sketch. Do not "
      .. "weaken the statement or take only a convenient sub-clause.",
    "",
    "----- theory atom (byte-exact statement + derivation) -----",
    tostring(candidate.atom_text),
  }, "\n")
  if #body > limits.body then
    return nil
  end
  return {
    schema = "github-proxy.issue-create.v1",
    repo = tostring(repo),
    title = title,
    body = body,
    labels = {},
    dedup_key = atom_marker,
    producer = bot_login,
    source_ref = {
      kind = "repo-site",
      ref = tostring(repo) .. "#theory-selfgrowth#digestion-atom#" .. tostring(candidate.atom_id),
    },
  }
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

local function body_text(dedup_key, bot_login)
  local producer_marker = M.producer_marker(bot_login)
  return table.concat({
    "Theory self-growth (CLAUDE.md 第22条 open-driven flywheel): the system PROPOSES a new",
    "mathematical truth AND proves it, growing the library. Deliver as ONE conservative increment.",
    "producer: " .. tostring(bot_login),
    "frontier-request-marker: " .. producer_marker,
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
    "trivial); pick a substantive claim. NOVELTY — search first; it must not already exist.",
    "CONSERVATIVE EXTENSION — append a new node only; never touch a frozen node.",
    "",
    "dedup-marker: " .. tostring(dedup_key),
  }, "\n")
end

return M
