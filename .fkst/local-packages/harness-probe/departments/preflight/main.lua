local M = {}

M.spec = {
  consumes = { "development-request" },
  produces = { "preflight-result" },
  stall_window = "30s",
}

local function require_non_empty_string(value, label)
  if type(value) ~= "string" or value == "" then
    error(label .. " must be a non-empty string", 2)
  end
  return value
end

function pipeline(event)
  if type(event) ~= "table" then
    error("development-request event must be a table", 2)
  end
  if event.queue ~= "harness-probe.development-request" then
    error("unexpected development-request queue", 2)
  end
  if type(event.payload) ~= "table" then
    error("development-request payload must be a table", 2)
  end
  if type(event.ts) ~= "number" then
    error("development-request ts must be a number", 2)
  end

  local request_source = require_non_empty_string(
    event.payload.raiser,
    "development-request payload.raiser")

  raise("preflight-result", {
    mode = "dry-run",
    status = "ready",
    request_source = request_source,
    request_ts = event.ts,
  })
end

return M
