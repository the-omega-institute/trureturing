local M = {}

local strings = require("contract.strings")

-- github-proxy.issue-create.v1 field bounds (mirror archaudit/core.lua limits).
local limits = {
  repo = 200,
  title = 240,
  body = 12000,
  dedup_key = 512,
  generation_key = 80,
  source_ref_kind = 80,
  source_ref_ref = 200,
}

-- Stable open-request marker; generation idempotency is scoped separately by
-- `idle-detector.system-idle.v1.detected_at`.
-- The devloop routes this exact title to `.fkst/workflows/frontier-generation.json`
-- (its POSITIVE FIXTURE is "Generate the next worthy D5 frontier obligation from the
-- current truth-DAG").
local REQUEST_MARKER = "theory-selfgrowth:frontier-request:v1"
local REQUEST_TITLE = "Generate the next worthy D5 frontier obligation from the current truth-DAG"

function M.request_marker() return REQUEST_MARKER end
function M.request_title() return REQUEST_TITLE end

function M.validate_repo(repo)
  if type(repo) ~= "string" then return false end
  return repo:match("^[%w._-]+/[%w._-]+$") ~= nil
end

local function assert_field(ok, name)
  if not ok then
    error("theory-selfgrowth: invalid-request-field: " .. tostring(name), 0)
  end
end

function M.iso_timestamp_epoch_seconds(timestamp)
  local year, month, day, hour, minute, second = tostring(timestamp or ""):match(
    "^(%d%d%d%d)%-(%d%d)%-(%d%d)T(%d%d):(%d%d):(%d%d)Z$"
  )
  if year == nil then
    return nil
  end
  year, month, day = tonumber(year), tonumber(month), tonumber(day)
  hour, minute, second = tonumber(hour), tonumber(minute), tonumber(second)
  if month < 1 or month > 12 or day < 1 or day > 31 or hour > 23 or minute > 59 or second > 59 then
    return nil
  end
  if month <= 2 then
    year = year - 1
    month = month + 12
  end
  local era = math.floor(year / 400)
  local year_of_era = year - era * 400
  local day_of_year = math.floor((153 * (month - 3) + 2) / 5) + day - 1
  local day_of_era = year_of_era * 365 + math.floor(year_of_era / 4) - math.floor(year_of_era / 100) + day_of_year
  return (era * 146097 + day_of_era - 719468) * 86400 + hour * 3600 + minute * 60 + second
end

local function is_bounded_marker_value(value, limit)
  return strings.is_bounded_string(value, limit)
    and tostring(value):find('[<>"\r\n]') == nil
end

local function invalid_idle(why)
  error("theory-selfgrowth: invalid-system-idle: " .. tostring(why), 0)
end

local function idle_payload(event)
  if type(event) ~= "table" then
    invalid_idle("event table required")
  end
  local queue = tostring(event.queue or "")
  if queue ~= "idle-detector.system_idle" and queue ~= "system_idle" then
    invalid_idle("unexpected queue " .. queue)
  end
  if type(event.payload) ~= "table" then
    invalid_idle("payload table required")
  end
  return event.payload
end

function M.validate_system_idle_event(event, now_seconds)
  local payload = idle_payload(event)
  if payload.schema ~= "idle-detector.system-idle.v1" then
    invalid_idle("schema must be idle-detector.system-idle.v1")
  end
  if not strings.is_bounded_string(payload.detected_at, limits.generation_key) then
    invalid_idle("detected_at required")
  end
  local detected_seconds = M.iso_timestamp_epoch_seconds(payload.detected_at)
  if detected_seconds == nil then
    invalid_idle("detected_at must be an ISO-8601 UTC second")
  end
  if not strings.is_bounded_string(payload.expires_at, limits.generation_key) then
    invalid_idle("expires_at required")
  end
  local expires_seconds = M.iso_timestamp_epoch_seconds(payload.expires_at)
  if expires_seconds == nil then
    invalid_idle("expires_at must be an ISO-8601 UTC second")
  end
  if type(now_seconds) ~= "number" then
    invalid_idle("now seconds required")
  end
  if expires_seconds <= now_seconds then
    invalid_idle("expired system_idle hint")
  end
  if type(payload.source_ref) ~= "table"
    or not strings.is_bounded_string(payload.source_ref.kind, limits.source_ref_kind)
    or not strings.is_bounded_string(payload.source_ref.ref, limits.source_ref_ref) then
    invalid_idle("source_ref required")
  end
  return payload
end

function M.generation_key(system_idle_payload)
  if type(system_idle_payload) ~= "table"
    or not is_bounded_marker_value(system_idle_payload.detected_at, limits.generation_key)
    or M.iso_timestamp_epoch_seconds(system_idle_payload.detected_at) == nil then
    error("theory-selfgrowth: invalid-generation-key: detected_at required", 0)
  end
  return tostring(system_idle_payload.detected_at)
end

function M.dedup_key(repo, generation_key)
  assert_field(M.validate_repo(repo), "repo")
  assert_field(is_bounded_marker_value(generation_key, limits.generation_key), "generation_key")
  return REQUEST_MARKER .. ":" .. tostring(repo) .. ":generation:" .. tostring(generation_key)
end

-- Open-only query for consumers that need to exclude an already-open request.
function M.open_request_search_query()
  return "in:body " .. REQUEST_MARKER .. " state:open"
end

local function body_text(repo, dedup_key)
  return table.concat({
    "Idle-triggered theory self-growth (CLAUDE.md 第22条 open-driven flywheel).",
    "",
    "Generate exactly ONE new dependency-ready D5 frontier obligation from the CURRENT",
    "frozen truth-DAG (machine Open-state via TruthDagConstruction.DeriveState; do NOT",
    "grep for `sorry`). Conservative extension only: append ONE X_Frontier task block",
    "(formal open statement + permanent D5-T#### + difficulty/deps/hint) and post exactly",
    "one downstream `Deliver ONE NEW D5 result` issue. Novelty dedup via live literature",
    "search stays in the Observe layer (receipts only); the admission gate is offline.",
    "",
    "This is the flywheel upstream (decide WHAT to prove next); it never touches a frozen node.",
    "",
    "open-request-marker: " .. REQUEST_MARKER,
    "dedup-marker: " .. tostring(dedup_key),
  }, "\n")
end

-- Build the github-proxy.issue-create.v1 request that routes to frontier-generation.
function M.build_frontier_request(repo, system_idle_payload)
  assert_field(M.validate_repo(repo), "repo")
  local generation_key = M.generation_key(system_idle_payload)
  local dedup_key = M.dedup_key(repo, generation_key)
  local title = REQUEST_TITLE
  local body = body_text(repo, dedup_key)
  local source_ref_ref = "theory-selfgrowth#frontier-generation-intent#" .. generation_key
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
