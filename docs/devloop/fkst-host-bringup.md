# fkst Host Bring-Up

This procedure installs the repository-owned maintenance launcher on a new macOS host. The
launcher runs once daily at 09:30 and always enters through `make hourly-maintenance` in the
dedicated checkout.

## 1. Prepare the checkout and host directories

Create a dedicated checkout at the absolute path that will become `FKST_HOST_ROOT`. Check out
the integration base used by this repository, then create the durable, runtime, log, launcher,
rate-pool, report-slot, worktree, and workflow-catalog directories named below. The launcher
directory must already exist before rendering.

## 2. Create the host file

Create one host-local file named `host.env` outside Git and set its mode to `0600`. Replace every
angle-bracket value below with a literal value for this machine. Values must not contain shell
expansions, command substitutions, or control operators. `PATH` must be a complete colon-separated
list of absolute directories; do not append `$PATH`.

```sh
BIN=<absolute-path-to-fkst-framework>
FKST_HOST_ROOT=<absolute-path-to-dedicated-checkout>
FKST_PLATFORM_ROOT=<absolute-path-to-platform-checkout>
FKST_DURABLE_ROOT=<absolute-path-to-durable-directory>
FKST_RUNTIME_ROOT=<absolute-path-to-runtime-directory>
FKST_RATE_POOL_ROOT=<absolute-path-to-rate-pool-directory>
FKST_WORKFLOW_CATALOG_ROOT=<absolute-path-to-workflow-catalog-directory>
PATH=<colon-separated-absolute-command-directories>
source "$FKST_HOST_ROOT/.fkst/deploy.env"
export FKST_GITHUB_BOT_LOGIN=<bot-login-for-this-machine>
export FKST_DEVLOOP_MANAGED_BOT_LOGINS=<comma-separated-managed-bot-logins>
export FKST_DEVLOOP_INTEGRATION_BRANCH=<integration-branch-for-this-machine>
export FKST_RUN_SCRIPT=<absolute-path-to-FKST_HOST_ROOT/.fkst/scripts/run.sh>
export FKST_MAINTENANCE_LOG=<absolute-path-to-maintenance-log>
export FKST_MAINTENANCE_LAUNCHER_LOG=<absolute-path-to-launchd-output-log>
export FKST_WORKTREE_ROOT=<absolute-path-to-runtime-worktrees>
export FKST_REPORT_SLOT_ROOT=<absolute-path-to-report-supervisor-slots>
export FKST_TIMEOUT_BIN=<absolute-path-to-timeout-command>
export FKST_LAUNCHD_LABEL=<loaded-supervisor-launchd-label>
export FKST_MAINTENANCE_LAUNCHD_LABEL=<maintenance-launchd-label-for-this-machine>
export FKST_MAINTENANCE_LAUNCHER_PATH=<absolute-path-to-rendered-maintenance-plist>
```

The `source` line is data to the strict maintenance parser: it must appear exactly as shown. The
parser resolves that one include and parses the versioned `.fkst/deploy.env` with the same
non-evaluating assignment grammar. Any other shell statement is rejected. The engine lifecycle
script still sources `host.env` because migration of the already-running supervise launcher is
outside this maintenance-launcher increment; keep this file within the restricted grammar so both
consumers receive the same values.

## 3. Validate and render

From `FKST_HOST_ROOT`, validate the complete contract without performing maintenance, then render
the plist to `FKST_MAINTENANCE_LAUNCHER_PATH`:

```sh
make hourly-maintenance HOST_CONFIG="<absolute-path-to-host.env>" VALIDATE_ONLY=1
make maintenance-launcher-render HOST_CONFIG="<absolute-path-to-host.env>"
plutil -lint "<absolute-path-to-rendered-maintenance-plist>"
```

Validation must exit zero. The rendered plist must name the new host's checkout, bot login, and
integration branch, and its program arguments must contain `hourly-maintenance` and
`HOST_CONFIG=<absolute-path-to-host.env>`.

## 4. Load the launcher

Use the user launchd domain. If this label has never been loaded, the `bootout` command may report
that no service exists; continue to `bootstrap`.

```sh
launchctl bootout "gui/$(id -u)" "<absolute-path-to-rendered-maintenance-plist>"
launchctl bootstrap "gui/$(id -u)" "<absolute-path-to-rendered-maintenance-plist>"
```

Do not copy the maintenance script into a host directory. The plist invokes the tracked Make
target in the dedicated checkout.

## 5. Verify deployment conformance

Run both checks after loading and after every checkout update that changes the contract, template,
or renderer:

```sh
make maintenance-launcher-check HOST_CONFIG="<absolute-path-to-host.env>"
launchctl print "gui/$(id -u)/<maintenance-launchd-label-for-this-machine>"
```

The first command exits zero only when the deployed plist is byte-for-byte identical to a fresh
render from the tracked template and this host's values. The second must show the same label,
09:30 calendar interval, log path, checkout path, bot login, and integration branch.
