-- theory-selfgrowth / propose department (CLAUDE.md 第22条 open-driven flywheel).
-- Fired by this package's own cron self-tick (theory_selfgrowth_tick, from
-- raisers/frontier_poll.lua). On each tick it emits at most ONE deduped frontier-generation
-- request; the #296 producer+generation-scoped dedup + open-request exclusion bound each
-- producer to one open request at a time. github-proxy performs the actual `gh issue create`.
--
-- Conformance shape (G10/G-DEAD-LETTER): a workflow.saga department. HOST-package form:
-- contract + publishable workflow/testkit + injected globals (exec_sync, raise, json, log).
-- The one raw `gh issue list` read (self-dedup search) is registered migration debt in
-- .fkst/conformance/allowlists/gh-git-adapter.allowlist (host packages cannot use forge).
local core = require("core")
local saga = require("workflow.saga")

local spec = {
  -- Own cron self-tick from raisers/frontier_poll.lua. (An idle-detector.system_idle trigger
  -- was dropped: idle_gate only broadcasts when the bot has zero self-assigned open issues,
  -- which never happens while any backlog is open, so it never fired — see core.poll_interval.)
  consumes = { "theory_selfgrowth_tick" },
  produces = { "github-proxy.github_issue_create_request" },
  stall_window = "30s",
  retry = false,
}

-- Read FKST_GITHUB_REPO via the injected `exec_sync` global (a `printf` of the env var).
local function read_repo()
  local out = exec_sync({ cmd = 'printf %s "$FKST_GITHUB_REPO"', timeout = 30 })
  if type(out) ~= "table" or out.exit_code ~= 0 then
    error("theory-selfgrowth: env-read-failed: FKST_GITHUB_REPO", 0)
  end
  return tostring(out.stdout or "")
end

-- Read FKST_GITHUB_BOT_LOGIN the same way as FKST_GITHUB_REPO. The producer marker must
-- always be scoped; fail closed when the runtime does not provide a sane bot identity.
local function read_bot_login()
  local out = exec_sync({ cmd = 'printf %s "$FKST_GITHUB_BOT_LOGIN"', timeout = 30 })
  if type(out) ~= "table" or out.exit_code ~= 0 then
    error("theory-selfgrowth: env-read-failed: FKST_GITHUB_BOT_LOGIN", 0)
  end
  return tostring(out.stdout or "")
end

-- Read the producer's OWN prior frontier-request issues (any state) so decide_generation can
-- compute the next generation and detect an active one. Comments carry github-devloop's
-- authoritative append-only state markers; labels are intentionally not fetched because they
-- are a fallible projection. Host-legal but forge-less: exec_sync + json.decode; registered as
-- gh-git-adapter migration debt. The search marker has no shell-special characters.
local function existing_requests(repo, bot_login)
  local cmd = "gh issue list --repo '" .. repo
    .. "' --state all --search '" .. core.marker_search_query(bot_login)
    .. "' --json number,state,body,comments --limit 1000"
  local out = exec_sync({ cmd = cmd, timeout = 30 })
  if type(out) ~= "table" or out.exit_code ~= 0 then
    error("theory-selfgrowth: request-search-failed: gh issue list", 0)
  end
  local ok, decoded = pcall(json.decode, tostring(out.stdout or "[]"))
  if not ok or type(decoded) ~= "table" then
    error("theory-selfgrowth: request-search-malformed-json: gh output is not a JSON array", 0)
  end
  return decoded
end

-- saga done(event): cheap, side-effect-free trigger validation. Idempotency (one open request
-- at a time) is enforced in act via the durable GitHub state, not cached here.
local function done(event)
  local queue = type(event) == "table" and tostring(event.queue or "") or ""
  if queue ~= "theory_selfgrowth_tick"
    and queue ~= "theory-selfgrowth.theory_selfgrowth_tick" then
    error("theory-selfgrowth: unknown-queue: " .. queue, 0)
  end
  return false
end

-- Read the digestion formalize-candidates projection (spec slice 1: the flywheel's formalize
-- target source is the digestion-ledger residual, not proposer's-choice). Host-legal but
-- forge-less: exec_sync + json.decode (mirrors the gh read above). Returns the candidates array,
-- or nil when the command fails / output is malformed (fail-closed -> honest no-op, never guess).
local function formalize_candidates()
  local out = exec_sync({ cmd = core.formalize_candidates_command(), timeout = 300 })
  if type(out) ~= "table" or out.exit_code ~= 0 then
    return nil
  end
  local ok, decoded = pcall(json.decode, tostring(out.stdout or "{}"))
  if not ok
    or type(decoded) ~= "table"
    or decoded.schema ~= "stratalint-formalize-candidates-v2"
    or type(decoded.candidates) ~= "table"
    or type(decoded.withheld) ~= "table" then
    return nil
  end
  return decoded.candidates
end

-- saga act(event): re-derive current GitHub state, then emit one digestion formalize-request if
-- none open. Selection is FIFO + generation round-robin over the ledger-derived candidate set
-- (fair coverage, not easy-first); the ledger decides residual membership, GitHub history only
-- provides per-atom attempt dedup. Empty/unavailable candidates or an oversize body => no-op.
local function act(_event)
  local repo = read_repo()
  if not core.validate_repo(repo) then
    error("theory-selfgrowth: malformed-repo: FKST_GITHUB_REPO is invalid: " .. tostring(repo), 0)
  end
  local bot_login = read_bot_login()
  if not core.validate_bot_login(bot_login) then
    error("theory-selfgrowth: malformed-bot-login: FKST_GITHUB_BOT_LOGIN is invalid: "
      .. tostring(bot_login), 0)
  end

  -- #296 Major 1: producer-scoped generation counter + per-producer open-request exclusion.
  local prior = existing_requests(repo, bot_login)
  local decision = core.decide_generation(prior, bot_login)
  if decision.open_exists then
    log.warn("theory-selfgrowth: an open frontier-request already exists for producer "
      .. bot_login .. "; skipping (one at a time)")
    return
  end

  local candidates = formalize_candidates()
  if candidates == nil then
    log.warn("theory-selfgrowth: formalize-candidates projection unavailable; skipping (no-op)")
    return
  end
  -- Round-robin over eligible candidates whose request body also fits the issue limit; an
  -- oversize candidate is skipped this round (never truncated), and the next admissible one is
  -- picked instead of no-op'ing.
  local candidate = core.select_candidate(candidates, decision.generation, prior, function(c)
    return core.build_frontier_request(repo, c, bot_login) ~= nil
  end)
  if candidate == nil then
    log.warn("theory-selfgrowth: no eligible digestion formalize candidate this round; no-op")
    return
  end

  raise("github-proxy.github_issue_create_request",
    core.build_frontier_request(repo, candidate, bot_login))
end

return saga.department(spec, {
  done = done,
  act = act,
  name = "propose",
})
