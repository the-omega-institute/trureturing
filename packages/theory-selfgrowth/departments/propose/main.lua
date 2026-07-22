-- theory-selfgrowth / propose department.
-- On the platform idle broadcast, emit ONE frontier-generation request, GENERATION-SCOPED
-- and gated by open-request exclusion so the self-growth flywheel keeps turning past its
-- first cycle (#296 Major 1) and never acts on a stale idle hint (#296 Major 2).
--
-- HOST-package form: publishable `contract` only, plus framework-injected globals
-- (`exec_sync` for shell reads, `json.decode` to parse, `raise` to produce, `log` to trace).
-- No forge/devloop/workflow_internal (platform-internal, unavailable to host packages).
-- The gh calls here are READS for the dedup decision; issue-create egress stays with
-- github-proxy, which still performs the actual create.

local core = require("core")

local M = {}

M.spec = {
  -- Two triggers (#346): this package's OWN cron self-tick (theory_selfgrowth_tick, from
  -- raisers/frontier_poll.lua) is what actually keeps the flywheel turning; the platform idle
  -- broadcast (idle-detector.system_idle) is kept as a secondary trigger. system_idle alone
  -- never fires (idle_gate requires zero self-assigned open issues), so an idle-only producer
  -- is structurally starved — see core.poll_interval.
  consumes = { "idle-detector.system_idle", "theory_selfgrowth_tick" },
  produces = { "github-proxy.github_issue_create_request" },
  stall_window = "30s",
  retry = false,
}

-- Is this our own periodic self-tick (vs the idle broadcast)? The self-tick carries no idle
-- payload, so it skips the idle-freshness assessment.
local function is_frontier_tick(event)
  local queue = type(event) == "table" and tostring(event.queue or "") or ""
  return queue == "theory_selfgrowth_tick" or queue == "theory-selfgrowth.theory_selfgrowth_tick"
end

-- Read FKST_GITHUB_REPO via the injected `exec_sync` global (a `printf` of the env var).
local function read_repo()
  local out = exec_sync({ cmd = 'printf %s "$FKST_GITHUB_REPO"', timeout = 30 })
  if type(out) ~= "table" or out.exit_code ~= 0 then
    error("theory-selfgrowth: env-read-failed: FKST_GITHUB_REPO", 0)
  end
  return tostring(out.stdout or "")
end

-- Current wall clock (UTC epoch seconds) for freshness assessment.
local function now_seconds()
  local out = exec_sync({ cmd = "date -u +%s", timeout = 30 })
  if type(out) ~= "table" or out.exit_code ~= 0 then
    error("theory-selfgrowth: clock-read-failed", 0)
  end
  local n = tonumber(tostring(out.stdout or ""):match("%d+"))
  if n == nil then
    error("theory-selfgrowth: clock-parse-failed", 0)
  end
  return n
end

-- Read the producer's OWN prior frontier-request issues (any state) so decide_generation
-- can compute the next generation and detect an open one. Host-legal: exec_sync + json.decode
-- (forge is platform-internal). The search marker contains no shell-special characters.
local function existing_requests(repo)
  local cmd = "gh issue list --repo '" .. repo
    .. "' --state all --search '" .. core.marker_search_query()
    .. "' --json number,state,body --limit 100"
  local out = exec_sync({ cmd = cmd, timeout = 30 })
  if type(out) ~= "table" or out.exit_code ~= 0 then
    error("theory-selfgrowth: request-search-failed", 0)
  end
  local ok, decoded = pcall(json.decode, tostring(out.stdout or "[]"))
  if not ok or type(decoded) ~= "table" then
    error("theory-selfgrowth: request-search-malformed-json", 0)
  end
  return decoded
end

function pipeline(event)
  -- The idle broadcast must not act on a stale/expired durable hint (#296 Major 2); the
  -- self-tick (#346) carries no idle payload and needs no freshness gate — it is this
  -- package's own fresh cron pulse.
  if not is_frontier_tick(event) then
    local verdict = core.assess_idle_payload(event and event.payload, now_seconds())
    if verdict == "malformed" then
      error("theory-selfgrowth: malformed system_idle payload", 0)
    end
    if verdict ~= "fresh" then
      log.warn("theory-selfgrowth: skipping " .. tostring(verdict) .. " system_idle hint")
      return
    end
  end

  local repo = read_repo()
  if not core.validate_repo(repo) then
    error("theory-selfgrowth: malformed FKST_GITHUB_REPO: " .. tostring(repo), 0)
  end

  -- #296 Major 1: generation-scoped dedup + open-request exclusion (one open at a time).
  local decision = core.decide_generation(existing_requests(repo))
  if decision.open_exists then
    log.warn("theory-selfgrowth: an open frontier-request already exists; skipping (one at a time)")
    return
  end

  -- Produce the issue-create event; github-proxy performs the gh call + dedup.
  raise("github-proxy.github_issue_create_request",
    core.build_frontier_request(repo, decision.generation))
end

return M
