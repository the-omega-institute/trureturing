-- Cron self-tick for the theory-selfgrowth flywheel (#346). Produces `theory_selfgrowth_tick`
-- on a fixed interval so the frontier producer has a trigger it actually receives, instead of
-- depending solely on `idle-detector.system_idle` (which requires zero self-assigned open
-- issues and therefore never fires while any backlog is open). The departments/propose
-- open-request exclusion bounds output to one open frontier-request at a time, so the tick
-- interval only sets how often the producer re-checks, never how many issues it creates.
local core = require("core")

return {
  type = "cron",
  interval = core.poll_interval(),
  produces = "theory_selfgrowth_tick",
}
