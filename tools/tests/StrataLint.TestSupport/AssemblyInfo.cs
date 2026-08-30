using System.Runtime.CompilerServices;

// 脚手架类型保持 internal(不扩大公开面),以具名 InternalsVisibleTo 供给两个消费者:
// 单元测试程序集与脚本测试程序集。目标④ 落地后,StrataLint.Tests 这一行将被删除,
// 届时「起真进程的能力」在结构上只对 ScriptTests 可见。
[assembly: InternalsVisibleTo("StrataLint.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]
