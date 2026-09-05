using System.Runtime.CompilerServices;

// 共享测试脚手架:TestProcessRunner 迁入 StrataLint.TestSupport 后需要
// BoundedProcessRunner / ProcessOutput / InfrastructureHangGuard 三个 internal 类型。
// **有真实消费者要求**:ScriptTests 17 处、ArchitectureTests 11 处跨项目使用(#5419 L3b)。
[assembly: InternalsVisibleTo("StrataLint.TestSupport")]
[assembly: InternalsVisibleTo("StrataLint.Tests")]
[assembly: InternalsVisibleTo("StrataLint.Engine.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]
[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]
[assembly: InternalsVisibleTo("StrataLint")]
[assembly: InternalsVisibleTo("StrataLint.Scribe")]
[assembly: InternalsVisibleTo("StrataLint.Scribe.Tests")]
[assembly: InternalsVisibleTo("StrataLint.EngineeringScope")]
