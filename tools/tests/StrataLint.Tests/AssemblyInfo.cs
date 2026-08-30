using System.Runtime.CompilerServices;

// 脚手架保持 internal 且单一归属于本程序集;脚本测试程序集经此具名可见性取用,
// 不复制源文件(共享编译项会被 SL-003 判 MSBuild Compile ownership ambiguous)。
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]
