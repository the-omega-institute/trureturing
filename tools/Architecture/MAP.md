# C# Architecture Rule Map

- `BannedSymbols.txt` is the culture-sensitive API denylist shared by Engine,
  Scribe, CLI, and the compile-fail proof project.
- `BannedSymbols.Determinism.txt` is the ambient time, entropy, and process-tick
  denylist shared by Engine, Scribe, CLI, and the compile-fail proof.
- `BannedSymbols.Guid.txt` is the GUID-creation denylist shared by deterministic
  Engine/Scribe code and the compile-fail proof. CLI is excluded because it creates
  ephemeral workspace names.
- Culture-sensitive enforcement covers parameterless `ToString`, one-argument
  `Parse`, and provider-less `TryParse` for the listed numeric and temporal types.
  Provider-bearing overloads remain available with `CultureInfo.InvariantCulture`.
- `HARDCODE-LEDGER.md` is the maintained guard/residual map. Every new hard-code
  family must update it in the same change.
- Golden case data is canonical TOML under `Golden/cases`; the architecture policy
  rejects literal-name case construction in C# while allowing loader/schema code.
- Contract-epoch obligation accounting keeps its parser/comparator in the base-owned
  conservative harness; exact-commit event/evidence data is closed and content-addressed,
  and P0 intentionally registers no transition plan.
- `Meta/FILEMAP.toml` is the five-kind repository custody manifest. ArchitectureTests
  enforce exact coverage, real producer/loader ownership, residence-epoch drift,
  directory purity, and the declared dependency-direction subset;
  `Generated/FILEMAP.md` is its emitted projection.

The official analyzer is dependency-admitted because compiler diagnostics enforce
source calls before binaries exist. Reflection remains sufficient for assembly and
type architecture, so ArchUnitNET and NetArchTest are not admitted.
