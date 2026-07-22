-- Package-scoped dead-letter handler (G-DEAD-LETTER): a package that consumes reliable
-- queues must consume the generic `dead_letter` queue. Mirrors archaudit's/idle-detector's
-- dead_letter department; workflow.dead_letter + workflow.saga are publishable host-legal.
local dead_letter = require("workflow.dead_letter")
local saga = require("workflow.saga")

local spec = {
  consumes = { "dead_letter" },
  produces = {},
  stall_window = "2m",
}

return saga.department(spec, dead_letter.handlers({
  package = "theory-selfgrowth",
}))
