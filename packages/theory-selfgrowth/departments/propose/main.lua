-- theory-selfgrowth / propose department.
-- Subscribes to the platform idle broadcast and emits ONE deduped frontier-generation
-- request when the D5 frontier has no open request. Modeled structurally on
-- fkst-packages/packages/archaudit/departments/audit/main.lua (idle-subscribed issue
-- producer via saga.department + ports_lib.install + global `raise`), minus codex.
--
-- DRAFT — pending fkst conformance-harness verification. Integration points marked
-- [VERIFY] mirror archaudit but must be confirmed against the platform's saga/ports
-- contracts before enabling (see README.md).

local core = require("core")
local saga = require("workflow.saga")
local ports_lib = require("forge.ports")
local github_factory = require("devloop.github_factory")
local env = require("workflow_internal.env")
local strings = require("contract.strings")

local spec = {
  -- system_idle is idle-detector's fanout broadcast; any package may subscribe.
  consumes = { "idle-detector.system_idle" },
  produces = { "github-proxy.github_issue_create_request" },
  stall_window = "30s",
  retry = false,
}

local allowed_env = { FKST_GITHUB_REPO = true }

local function read_env_command(name)
  if not allowed_env[name] then
    error("theory-selfgrowth: env-name-denied: " .. tostring(name), 0)
  end
  return 'printf %s "$' .. name .. '"'
end
-- [VERIFY] env.read_env signature mirrors idle-detector/idle_gate/main.lua.
local read_env = env.read_env(read_env_command, { propagate_exec_errors = true })

local function fail(error_class, message)
  error(("theory-selfgrowth: " .. tostring(error_class) .. ": " .. tostring(message)), 0)
end

local function repo_from_env()
  local repo = strings.trim(read_env("FKST_GITHUB_REPO") or "")
  if repo == "" then return nil, "missing-repo", "missing FKST_GITHUB_REPO" end
  if not core.validate_repo(repo) then return nil, "malformed-repo", "malformed FKST_GITHUB_REPO" end
  return repo, nil, nil
end

-- Dedup: is a generation request already open? (at most one at a time → no flood)
-- [VERIFY] github.issue_search(repo, query, fields, limit) mirrors archaudit's use.
local function has_open_request(github, repo)
  local issues = github.issue_search(repo, core.open_request_search_query(), "number,title,state,body", 5)
  for _, issue in ipairs(issues or {}) do
    if tostring(issue.state or ""):lower() == "open" then
      return true
    end
  end
  return false
end

-- [VERIFY] make_department(ports) + global `raise` mirror archaudit's make_department.
local function make_department(ports)
  local function act_propose(event)
    local repo, ec, em = repo_from_env()
    if repo == nil then fail(ec, em) end
    local ok, existing = pcall(has_open_request, ports.github, repo)
    if not ok then fail("search-failure", tostring(existing)) end
    if existing then
      return -- terminal no-op: a generation request is already open (verified replay)
    end
    raise("github-proxy.github_issue_create_request", core.build_frontier_request(repo))
  end

  -- Idempotent: the dedup search guards duplicates, so completion is unconditional.
  local function propose_done(_event)
    return true
  end

  local department = saga.department(spec, {
    done = propose_done,
    act = act_propose,
    name = "propose",
  })
  department.ports = ports
  return department
end

-- [VERIFY] exec_sync is a module-scope global primitive (as in archaudit).
return ports_lib.install(make_department, github_factory.github_options(exec_sync))
