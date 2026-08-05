local core = require("core")
local t = fkst.test

local DEFAULT_AUTHORITY_ROOT = "/Users/auric/fkst-packages/packages/github-proxy"
local AUTHORITY_ROOT_ENV = "FKST_GITHUB_PROXY_AUTHORITY_ROOT"
local CONTRACT_FIELDS = {
  "repo",
  "title",
  "body",
  "dedup_key",
  "source_ref_kind",
  "source_ref_ref",
}

local function read_file(path)
  local handle, err = io.open(path, "r")
  if handle == nil then
    return nil, err
  end
  local contents = handle:read("*a")
  handle:close()
  return contents
end

local function deployed_authority_limits(root)
  local issue_create_path = root .. "/core/issue_create.lua"
  local issue_create_source, err = read_file(issue_create_path)
  if issue_create_source == nil then
    return nil, "deployed authority is unreachable at " .. issue_create_path .. ": " .. tostring(err)
  end

  assert(issue_create_source:find(
    'require("contract.github_issue_create").limits()', 1, true) ~= nil,
    "deployed github-proxy no longer obtains issue-create limits from contract.github_issue_create")

  local contract_path = root .. "/../../libraries/contract/github_issue_create.lua"
  local contract_source, contract_err = read_file(contract_path)
  assert(contract_source ~= nil,
    "deployed github-proxy authority contract is unreadable at " .. contract_path
      .. ": " .. tostring(contract_err))
  local field_limits_source = contract_source:match("local%s+field_limits%s*=%s*(%b{})")
  assert(field_limits_source ~= nil,
    "deployed github-proxy authority contract has no field_limits table: " .. contract_path)
  return restricted_lua_load({
    source = "return " .. field_limits_source,
    name = "github-proxy.issue-create.v1 field limits",
  })
end

local function assert_no_absent_package_reference(path)
  local source = assert(read_file(path))
  local absent_package = "archa" .. "udit"
  assert(source:lower():find(absent_package, 1, true) == nil,
    path .. " cites a package absent from this composition")
  return source
end

return {
  test_local_issue_create_limits_match_deployed_authority = function()
    local authority_root = os.getenv(AUTHORITY_ROOT_ENV) or DEFAULT_AUTHORITY_ROOT
    local authority, skip_reason = deployed_authority_limits(authority_root)
    if authority == nil then
      io.stderr:write("SKIP theory-selfgrowth github-proxy contract drift check: "
        .. skip_reason .. "\n")
      return
    end

    assert(type(core.issue_create_limits) == "function",
      "the local github-proxy.issue-create.v1 copy is not inspectable for drift checking")
    local copied = core.issue_create_limits()
    for _, field in ipairs(CONTRACT_FIELDS) do
      t.eq(copied[field], authority[field])
    end
  end,

  test_missing_deployed_authority_is_classified_for_loud_skip = function()
    local authority, reason = deployed_authority_limits(
      "/path/that/does/not/exist/github-proxy")
    t.eq(authority, nil)
    assert(reason:find("deployed authority is unreachable", 1, true) ~= nil)
  end,

  test_package_sources_name_reachable_contracts_not_absent_packages = function()
    local core_source = assert_no_absent_package_reference(
      "packages/theory-selfgrowth/core.lua")
    assert_no_absent_package_reference(
      "packages/theory-selfgrowth/departments/dead_letter/main.lua")
    assert_no_absent_package_reference(
      "packages/theory-selfgrowth/tests/run_graph_frontier_poll_fire_raiser_test.lua")
    assert_no_absent_package_reference(
      "packages/theory-selfgrowth/README.md")

    assert(core_source:find(
      "Local copy of the deployed github-proxy.issue-create.v1 field boundaries.", 1, true) ~= nil,
      "the local issue-create limits are not explicitly marked as a deployed-contract copy")
    assert(core_source:find(
      "tests/github_issue_create_contract_drift_test.lua", 1, true) ~= nil,
      "the local issue-create limits do not name their machine drift check")
  end,
}
