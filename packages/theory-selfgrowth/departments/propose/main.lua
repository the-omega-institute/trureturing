-- theory-selfgrowth / propose department.
-- On the platform idle broadcast, emit ONE frontier-generation request. github-proxy
-- dedups on the request's stable `dedup_key`, so at most one open request exists at a
-- time (no flood) — this department needs no github search of its own.
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

function pipeline(_event)
  local repo = read_repo()
  if not core.validate_repo(repo) then
    error("theory-selfgrowth: malformed FKST_GITHUB_REPO: " .. tostring(repo), 0)
  end
  -- Produce the issue-create event; github-proxy performs the gh call + dedup.
  raise("github-proxy.github_issue_create_request", core.build_frontier_request(repo))
end

return M
