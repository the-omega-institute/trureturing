local t = fkst.test

local function tick(raiser)
  return {
    queue = "dry-run-tick",
    payload = { raiser = raiser or "dry_run_tick" },
  }
end

local function mock_env(repo, write)
  t.mock_command('printf %s "$FKST_GITHUB_REPO"', {
    stdout = repo or "the-omega-institute/trureturing",
    stderr = "",
    exit_code = 0,
  })
  t.mock_command('printf %s "$FKST_GITHUB_WRITE"', {
    stdout = write or "",
    stderr = "",
    exit_code = 0,
  })
end

local function assert_rejected(event, expected)
  local result = t.run_department("departments/dry_run_guard/main.lua", event)
  t.eq(result.exit_code, 1)
  t.is_true(string.find(result.error or "", expected, 1, true) ~= nil)
  t.is_nil(result.raises[1])
end

return {
  test_accepts_trureturing_dry_run_without_side_effects = function()
    mock_env()
    local result = t.run_department("departments/dry_run_guard/main.lua", tick())
    t.eq(result.exit_code, 0)
    t.is_nil(result.raises[1])
  end,

  test_accepts_namespaced_supervise_raiser = function()
    mock_env()
    local result = t.run_department(
      "departments/dry_run_guard/main.lua",
      tick("trureturing-devtask.dry_run_tick"))
    t.eq(result.exit_code, 0)
    t.is_nil(result.raises[1])
  end,

  test_rejects_write_posture = function()
    mock_env(nil, "1")
    assert_rejected(tick(), "GitHub write posture is forbidden")
  end,

  test_rejects_wrong_repo = function()
    mock_env("owner/other")
    assert_rejected(tick(), "unexpected GitHub repository")
  end,

  test_rejects_wrong_raiser = function()
    mock_env()
    assert_rejected(tick("other"), "dry-run tick must originate from dry_run_tick")
  end,
}
