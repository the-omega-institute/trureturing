using System.Runtime.CompilerServices;

[assembly: InternalsVisibleTo("StrataLint.EngineeringScope.Tests")]

// ArchitectureTests asserts ControllerClosure's pure snapshot derivation directly.
// Reaching it by reflection instead makes ScribeTestMapDeriver record those methods as
// conservative unknown, which SL-003 blocks per introduced identity; a direct call keeps
// the same assertions statically resolvable.
[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]
