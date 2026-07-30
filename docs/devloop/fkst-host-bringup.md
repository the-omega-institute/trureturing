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
export FKST_BASH_BIN=<absolute-path-to-bash>
export FKST_ZSH_BIN=<absolute-path-to-zsh>
export FKST_PYTHON_BIN=<absolute-path-to-python3>
export FKST_SUPERVISE_LAUNCHER_LOG=<absolute-path-to-supervise-launchd-output-log>
export FKST_SUPERVISE_LAUNCHER_PATH=<absolute-path-to-rendered-supervise-plist>
```

The `source` line is data to the strict maintenance parser: it must appear exactly as shown. It
declares exactly one repository-data include, but the parser reads `.fkst/deploy.env` beside its
own tracked scripts rather than following `FKST_HOST_ROOT`. The parser, schema, and repository
data therefore always come from one revision. A normal invocation from `FKST_HOST_ROOT` validates
the deployed copy; during a cutover invoked from a newer checkout, the newer contract is validated
without letting the stale deployed copy block its own refresh. The file uses the same
non-evaluating assignment grammar, and any other shell statement is rejected. The engine
lifecycle script still sources `host.env` because migration of the already-running supervise
launcher is outside this maintenance-launcher increment; keep this file within the restricted
grammar so both consumers receive the same values.

Existing hosts must add the five supervise provider keys above to their operator-owned
`host.env` before the first maintenance cycle using this revision. Do not edit the file from a
repository migration. The periodic conformance gate fails closed when any provider key is absent
and names the missing key as `required host key <KEY> is unset`; it never skips the affected unit.

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

Run the inventory-wide conformance check after loading and after every checkout update that
changes the contract, a launchd template, or a renderer:

```sh
make launchd-conformance-check HOST_CONFIG="<absolute-path-to-host.env>"
launchctl print "gui/$(id -u)/<maintenance-launchd-label-for-this-machine>"
```

The first command exits zero only when host launchd membership exactly matches the repository
inventory and every deployed plist is byte-for-byte identical to a fresh render from the tracked
template and this host's values. `make hourly-maintenance` delegates this same gate after its
normal cycle and propagates any gate failure as a failed periodic run. The second command must
show the same label, 09:30 calendar interval, log path, checkout path, bot login, and integration
branch.
