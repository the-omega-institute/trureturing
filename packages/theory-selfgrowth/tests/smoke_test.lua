local core = require("core")
local t = fkst.test

return {
  test_builds_frontier_request_for_declared_host_package = function()
    local request = core.build_frontier_request("owner/repo")

    t.eq(request.schema, "github-proxy.issue-create.v1")
    t.eq(request.repo, "owner/repo")
    t.eq(request.title, core.request_title())
  end,
}
