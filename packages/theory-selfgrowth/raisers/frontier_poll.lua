-- Periodic reconciliation for the theory-selfgrowth flywheel (#346). This package-owned wakeup
-- remains reachable under sustained backlog. The propose department separately bounds output
-- to one open frontier request, so the interval controls detection latency, not issue volume.
local core = require("core")

return {
  type = "cron",
  interval = core.poll_interval(),
  produces = "theory_selfgrowth_tick",
}
