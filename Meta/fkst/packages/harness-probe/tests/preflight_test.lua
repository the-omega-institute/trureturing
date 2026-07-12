local t = fkst.test

local function assert_rejected(event, expected_error)
  local result = t.run_department("departments/preflight/main.lua", event)

  t.eq(result.exit_code, 1)
  t.is_true(string.find(
    result.error or "",
    expected_error,
    1,
    true) ~= nil)
  t.is_nil(result.raises[1])
end

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

  test_preflight_rejects_non_table_event = function()
    assert_rejected(false, "development-request event must be a table")
  end,

  test_preflight_rejects_wrong_queue = function()
    assert_rejected({
      queue = 42,
      payload = { raiser = "development_request" },
      ts = 123,
    }, "unexpected development-request queue")
  end,

  test_preflight_rejects_non_table_payload = function()
    assert_rejected({
      queue = "development-request",
      payload = "invalid",
      ts = 123,
    }, "development-request payload must be a table")
  end,

  test_preflight_rejects_non_numeric_ts = function()
    assert_rejected({
      queue = "development-request",
      payload = { raiser = "development_request" },
      ts = "123",
    }, "development-request ts must be a number")
  end,

  test_preflight_rejects_missing_request_source = function()
    assert_rejected({
      queue = "development-request",
      payload = {},
      ts = 123,
    }, "development-request payload.raiser must be a non-empty string")
  end,

  test_preflight_rejects_wrong_type_request_source = function()
    assert_rejected({
      queue = "development-request",
      payload = { raiser = false },
      ts = 123,
    }, "development-request payload.raiser must be a non-empty string")
  end,

  test_preflight_rejects_empty_request_source = function()
    assert_rejected({
      queue = "development-request",
      payload = { raiser = "" },
      ts = 123,
    }, "development-request payload.raiser must be a non-empty string")
  end,
}
