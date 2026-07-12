# C# Architecture Rule Map

- `BannedSymbols.txt` is the single deterministic-API denylist shared by Engine,
  Scribe, and the compile-fail proof project.
- Time, entropy, process-tick, and GUID creation APIs are forbidden outright.
- Culture-sensitive enforcement covers parameterless `ToString`, one-argument
  `Parse`, and provider-less `TryParse` for the listed numeric and temporal types.
  Provider-bearing overloads remain available with `CultureInfo.InvariantCulture`.

The official analyzer is dependency-admitted because compiler diagnostics enforce
source calls before binaries exist. Reflection remains sufficient for assembly and
type architecture, so ArchUnitNET and NetArchTest are not admitted.
