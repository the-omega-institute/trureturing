-- theory-selfgrowth / propose department.
-- On a fresh platform idle broadcast, emit ONE frontier-generation request. The
-- request `dedup_key` is scoped to the validated idle generation so a closed prior
-- generation cannot suppress a later one.
--
-- HOST-package form: publishable `contract` only, plus framework-injected globals
-- (`exec_sync` to read FKST_GITHUB_REPO, `raise` to produce). No forge/devloop/
-- workflow_internal (platform-internal). Egress stays with github-proxy.

local core = require("core")

local M = {}

M.spec = {
  -- system_idle is idle-detector's fanout broadcast; any package may subscribe.
  consumes = { "idle-detector.system_idle" },
  produces = { "github-proxy.github_issue_create_request" },
  stall_window = "30s",
  retry = false,
}

-- Read FKST_GITHUB_REPO via the injected `exec_sync` global (same mechanism the
-- platform's workflow_internal.env wraps: a `printf` of the env var, then read stdout).
local function read_repo()
  local out = exec_sync({ cmd = 'printf %s "$FKST_GITHUB_REPO"', timeout = 30 })
  if type(out) ~= "table" or out.exit_code ~= 0 then
    error("theory-selfgrowth: env-read-failed: FKST_GITHUB_REPO", 0)
  end
  return tostring(out.stdout or "")
end

local function current_now_seconds()
  if type(now) ~= "function" then
    error("theory-selfgrowth: now-unavailable: now primitive is required", 0)
  end
  local seconds = tonumber(now())
  if seconds == nil then
    error("theory-selfgrowth: now-unavailable: now primitive returned non-numeric value", 0)
  end
  return seconds
end

function pipeline(event)
  local idle_payload = core.validate_system_idle_event(event, current_now_seconds())
  local repo = read_repo()
  if not core.validate_repo(repo) then
    error("theory-selfgrowth: malformed FKST_GITHUB_REPO: " .. tostring(repo), 0)
  end
  -- Produce the issue-create event; github-proxy performs the gh call + dedup.
  raise("github-proxy.github_issue_create_request", core.build_frontier_request(repo, idle_payload))
end

return M
