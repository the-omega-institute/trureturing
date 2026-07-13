local M = {}

M.spec = {
  consumes = { "dry-run-tick" },
  produces = {},
  stall_window = "30s",
}

local allowed_env = {
  FKST_GITHUB_REPO = true,
  FKST_GITHUB_WRITE = true,
}

local function read_env_command(name)
  if not allowed_env[name] then
    error("trureturing-devtask: env name denied", 2)
  end
  return 'printf %s "$' .. name .. '"'
end

local function read_env(name)
  if type(exec_sync) ~= "function" then
    error("trureturing-devtask: exec_sync unavailable", 2)
  end
  local result = exec_sync(read_env_command(name))
  if type(result) ~= "table" or result.exit_code ~= 0 then
    error("trureturing-devtask: environment read failed", 2)
  end
  return result.stdout or ""
end

function M.format_posture(repo, write)
  local posture = write == "1" and "live" or "dry-run"
  return "trureturing-devtask posture repo=" .. repo .. " write=" .. posture
end

function pipeline(event)
  if type(event) ~= "table" then
    error("dry-run tick must be a table", 2)
  end
  if event.queue ~= "trureturing-devtask.dry-run-tick" then
    error("unexpected dry-run queue", 2)
  end
  local raiser = type(event.payload) == "table" and event.payload.raiser or nil
  if raiser ~= "dry_run_tick" and raiser ~= "trureturing-devtask.dry_run_tick" then
    error("dry-run tick must originate from dry_run_tick", 2)
  end

  local repo = read_env("FKST_GITHUB_REPO")
  if repo ~= "the-omega-institute/trureturing" then
    error("unexpected GitHub repository", 2)
  end
  print(M.format_posture(repo, read_env("FKST_GITHUB_WRITE")))
end

return M
