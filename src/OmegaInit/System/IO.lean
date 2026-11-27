module
public import Init.System.IO

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (IO.TaskState)
end Omega
namespace Omega.IO.FS
export _root_.IO.FS (FileType Mode)
end Omega.IO.FS
namespace Omega.IO.FS.FileType
export _root_.IO.FS.FileType (dir file other rec recOn symlink)
end Omega.IO.FS.FileType
namespace Omega.IO.FS.Mode
export _root_.IO.FS.Mode (append read readWrite rec recOn write writeNew)
end Omega.IO.FS.Mode
namespace Omega.IO.Process
export _root_.IO.Process (Stdio)
end Omega.IO.Process
namespace Omega.IO.Process.Stdio
export _root_.IO.Process.Stdio (inherit null piped rec recOn)
end Omega.IO.Process.Stdio
namespace Omega.IO.TaskState
export _root_.IO.TaskState (finished rec recOn running waiting)
end Omega.IO.TaskState
