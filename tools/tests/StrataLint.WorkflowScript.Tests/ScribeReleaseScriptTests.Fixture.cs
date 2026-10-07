using StrataLint.Runtime;
using StrataLint.Engine;

namespace StrataLint.WorkflowScript.Tests;

public sealed partial class ScribeReleaseScriptTests
{
    private sealed class Fixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string bin;
        private readonly string cloud;
        private readonly string events;
        private readonly string fault;

        internal Fixture(string fault = "")
        {
            this.fault = fault;
            repository = Path.Combine(temporary.Path, "repository");
            bin = Path.Combine(temporary.Path, "bin");
            cloud = Path.Combine(temporary.Path, "cloud");
            events = Path.Combine(temporary.Path, "events");
            Directory.CreateDirectory(bin);
            Directory.CreateDirectory(cloud);
            Directory.CreateDirectory(Path.Combine(repository, "Blueprint"));
            Directory.CreateDirectory(Path.Combine(repository, "tools/scripts"));
            Directory.CreateDirectory(Path.Combine(repository, "tools/StrataLint.Scribe"));
            File.WriteAllText(Path.Combine(repository, "global.json"), "{}");
            File.WriteAllText(Path.Combine(repository, "tools/StrataLint.Scribe/StrataLint.Scribe.csproj"), "<Project />");
            File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/scribe-release.sh"),
                Path.Combine(repository, "tools/scripts/scribe-release.sh"));
            File.WriteAllText(events, "");
            File.WriteAllText(Path.Combine(cloud, "state"), "missing");
            Install("dotnet", Dotnet);
            Install("gh", Gh);
        }

        internal string[] Events => File.ReadAllLines(events);
        internal string State => File.ReadAllText(Path.Combine(cloud, "state")).Trim();
        internal string FetchDirectory => Path.Combine(temporary.Path, "fetched");
        internal bool HasAsset(string name) => File.Exists(Path.Combine(cloud, name));

        internal void Published(bool includeCarrier = true)
        {
            File.WriteAllText(Path.Combine(cloud, "state"), "false");
            File.WriteAllText(Path.Combine(cloud, Pack), "resource-pack");
            if (includeCarrier) File.WriteAllText(Path.Combine(cloud, Carrier), "resource-pack");
        }

        internal ProcessOutput Publish() => Run(["publish", "--target", new string('c', 40)]);
        internal ProcessOutput Fetch() => Run(["fetch", Digest, "--out", FetchDirectory]);

        private ProcessOutput Run(string[] arguments) => TestProcessRunner.Run("/bin/bash",
            ["-c", "export PATH=\"$1:$PATH\" FIXTURE_CLOUD=\"$2\" FIXTURE_EVENTS=\"$3\" FIXTURE_FAULT=\"$4\" FIXTURE_DIGEST=\"$5\" SCRIBE_RELEASE_REPO=fixture/repository; shift 5; exec /bin/bash \"$@\"",
                "scribe-release-test", bin, cloud, events, fault, Digest,
                Path.Combine(repository, "tools/scripts/scribe-release.sh"), .. arguments],
            repository, TestBudgets.ScriptProcessHangGuard, 64 * 1024);

        private void Install(string name, string text)
        {
            if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException("the shell fixture requires Unix");
            var path = Path.Combine(bin, name);
            File.WriteAllText(path, text);
            File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        public void Dispose() => temporary.Dispose();

        private const string Dotnet = """
            #!/usr/bin/env bash
            set -euo pipefail
            if [[ "$1" == --version ]]; then printf '10.0.100\n'; exit 0; fi
            while [[ "$1" != -- ]]; do shift; done
            shift
            [[ "$1" == resources ]] || exit 90
            command="$2" directory="$4"
            pack=scribe-resources.zip carrier=StrataLint.Scribe.ResourceBundle.dll
            case "$command" in
              release)
                printf 'build\n' >> "$FIXTURE_EVENTS"
                mkdir -p "$directory"
                printf resource-pack > "$directory/$pack"
                printf resource-pack > "$directory/$carrier"
                ;;
              verify-release)
                phase=downloaded
                [[ "$directory" != */Generated/scribe-release ]] || phase=local
                printf 'verify-release %s\n' "$phase" >> "$FIXTURE_EVENTS"
                [[ -f "$directory/$pack" && -f "$directory/$carrier" ]] || exit 6
                cmp -s "$directory/$pack" "$directory/$carrier" || exit 7
                digest="$FIXTURE_DIGEST"
                if [[ "$phase" == downloaded ]]; then
                  case "$FIXTURE_FAULT" in
                    verify) exit 7 ;;
                    digest) digest="${digest//a/b}" ;;
                    missing-digest) printf 'verified\n'; exit 0 ;;
                  esac
                fi
                printf 'verified totalSha256=%s\n' "$digest"
                ;;
              verify)
                printf 'verify-pack\n' >> "$FIXTURE_EVENTS"
                [[ -f "$directory" ]] || exit 6
                printf 'verified totalSha256=%s\n' "$FIXTURE_DIGEST"
                ;;
              *) exit 91 ;;
            esac
            """;

        private const string Gh = """
            #!/usr/bin/env bash
            set -euo pipefail
            [[ "$1" == release ]] || exit 90
            command="$2"
            shift 3
            case "$command" in
              view)
                state="$(cat "$FIXTURE_CLOUD/state")"
                printf 'view %s\n' "$state" >> "$FIXTURE_EVENTS"
                [[ "$state" != missing ]] || { printf 'release not found\n' >&2; exit 1; }
                printf '%s\n' "$state"
                ;;
              create)
                printf 'create\n' >> "$FIXTURE_EVENTS"
                printf true > "$FIXTURE_CLOUD/state"
                [[ "$FIXTURE_FAULT" != create ]] || exit 5
                ;;
              upload)
                while [[ "$#" -gt 0 && "$1" != --* ]]; do
                  name="$(basename "$1")"
                  printf 'upload %s\n' "$name" >> "$FIXTURE_EVENTS"
                  cp "$1" "$FIXTURE_CLOUD/$name"
                  shift
                  [[ "$FIXTURE_FAULT" != upload ]] || exit 5
                done
                ;;
              download)
                pattern= directory=
                while [[ "$#" -gt 0 ]]; do
                  case "$1" in
                    --pattern) pattern="$2" ;;
                    --dir) directory="$2" ;;
                    --repo) ;;
                    *) exit 91 ;;
                  esac
                  shift 2
                done
                printf 'download %s\n' "$pattern" >> "$FIXTURE_EVENTS"
                [[ "$FIXTURE_FAULT" != download ]] || exit 5
                [[ -f "$FIXTURE_CLOUD/$pattern" ]] || exit 6
                cp "$FIXTURE_CLOUD/$pattern" "$directory/$pattern"
                if [[ "$FIXTURE_FAULT" == corrupt-carrier && "$pattern" == *.dll ]]; then
                  printf inconsistent > "$directory/$pattern"
                fi
                ;;
              edit)
                printf 'edit\n' >> "$FIXTURE_EVENTS"
                [[ "$FIXTURE_FAULT" != edit ]] || exit 5
                printf false > "$FIXTURE_CLOUD/state"
                ;;
              delete)
                printf 'delete\n' >> "$FIXTURE_EVENTS"
                rm -f "$FIXTURE_CLOUD/scribe-resources.zip" "$FIXTURE_CLOUD/StrataLint.Scribe.ResourceBundle.dll"
                printf missing > "$FIXTURE_CLOUD/state"
                ;;
              *) exit 92 ;;
            esac
            """;
    }
}
