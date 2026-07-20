local M = {}

local strings = require("contract.strings")

-- github-proxy.issue-create.v1 field bounds (mirror archaudit/core.lua limits).
local limits = {
  repo = 200,
  title = 240,
  body = 12000,
  dedup_key = 512,
  source_ref_kind = 80,
  source_ref_ref = 200,
}

-- Stable marker so at most ONE open generation request exists at a time (dedup).
-- The devloop routes this exact title to `.fkst/workflows/frontier-generation.json`
-- (its POSITIVE FIXTURE is "Generate the next worthy D5 frontier obligation from the
-- current truth-DAG").
local REQUEST_MARKER = "theory-selfgrowth:frontier-request:v1"
local REQUEST_TITLE = "Generate the next worthy D5 frontier obligation from the current truth-DAG"

function M.request_marker() return REQUEST_MARKER end
function M.request_title() return REQUEST_TITLE end

-- Idempotency key handed to github-proxy: one open request per repo at a time.
function M.dedup_key(repo)
  return REQUEST_MARKER .. ":" .. tostring(repo)
end

-- Search query github-proxy uses to detect an already-open request (dedup).
function M.open_request_search_query()
  return "in:body " .. REQUEST_MARKER .. " state:open"
end

function M.validate_repo(repo)
  if type(repo) ~= "string" then return false end
  return repo:match("^[%w._-]+/[%w._-]+$") ~= nil
end

local function assert_field(ok, name)
  if not ok then
    error("theory-selfgrowth: invalid-request-field: " .. tostring(name), 0)
  end
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
    "dedup-marker: " .. tostring(dedup_key),
  }, "\n")
end

-- Build the github-proxy.issue-create.v1 request that routes to frontier-generation.
function M.build_frontier_request(repo)
  assert_field(M.validate_repo(repo), "repo")
  local dedup_key = M.dedup_key(repo)
  local title = REQUEST_TITLE
  local body = body_text(repo, dedup_key)
  local source_ref_ref = tostring(repo) .. "#theory-selfgrowth#frontier-generation-intent"
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
