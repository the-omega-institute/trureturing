local t = fkst.test

return {
  test_preflight_emits_dry_run_result = function()
    local result = t.run_department("departments/preflight/main.lua", {
      queue = "development-request",
      payload = { raiser = "development_request" },
      ts = 123,
    })

    t.eq(result.exit_code, 0)
    t.eq(result.raises[1].queue, "harness-probe.preflight-result")
    t.eq(result.raises[1].payload.mode, "dry-run")
    t.eq(result.raises[1].payload.status, "ready")
    t.eq(result.raises[1].payload.request_source, "development_request")
    t.is_nil(result.raises[2])
  end,

  test_preflight_rejects_missing_request_source = function()
    local result = t.run_department("departments/preflight/main.lua", {
      queue = "development-request",
      payload = {},
      ts = 123,
    })

    t.eq(result.exit_code, 1)
    t.is_true(string.find(
      result.error or "",
      "development-request payload.raiser must be a non-empty string",
      1,
      true) ~= nil)
    t.is_nil(result.raises[1])
  end,
}
