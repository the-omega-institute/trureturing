module
prelude
public import OmegaInit.System.IO

public inductive PathStatus where
  | ok
  | existsAlready (filename : Omega.Option Omega.String) (code : Omega.UInt32) (details : Omega.String)
  | missing (filename : Omega.String) (code : Omega.UInt32) (details : Omega.String)
  | other

public abbrev PathWorld := Omega.Void Omega.IO.RealWorld
public abbrev PathResult := Omega.Prod PathStatus PathWorld

private def observe (out : Omega.EST.Out Omega.IO.Error Omega.IO.RealWorld Omega.Unit) : PathResult :=
  match out with
  | .ok _ world => ⟨.ok, world⟩
  | .error error world =>
    let status := match error with
      | .alreadyExists path code details => PathStatus.existsAlready path code details
      | .noFileOrDirectory path code details => PathStatus.missing path code details
      | _ => PathStatus.other
    ⟨status, world⟩

@[export omega_test_path_env] public def pathEnv (key : Omega.String) (w : PathWorld) :=
  Omega.IO.getEnv key w
@[export omega_test_path_create] public def pathCreate (p : Omega.String) (w : PathWorld) : PathResult :=
  observe (Omega.IO.FS.createDir ⟨p⟩ w)
@[export omega_test_path_rmdir] public def pathRemoveDir (p : Omega.String) (w : PathWorld) : PathResult :=
  observe (Omega.IO.FS.removeDir ⟨p⟩ w)
@[export omega_test_path_unlink] public def pathRemoveFile (p : Omega.String) (w : PathWorld) : PathResult :=
  observe (Omega.IO.FS.removeFile ⟨p⟩ w)
@[export omega_test_path_rename] public def pathRename (p q : Omega.String) (w : PathWorld) : PathResult :=
  observe (Omega.IO.FS.rename ⟨p⟩ ⟨q⟩ w)

@[export omega_test_path_hard_link] public def pathHardLink (p q : Omega.String) (w : PathWorld) : PathResult :=
  observe (Omega.IO.FS.hardLink ⟨p⟩ ⟨q⟩ w)
@[export omega_test_path_set_cwd] public def pathSetCwd (p : Omega.String) (w : PathWorld) : PathResult :=
  observe (Omega.IO.Process.setCurrentDir ⟨p⟩ w)
@[export omega_test_path_cwd] public def pathCwd (w : PathWorld) := Omega.IO.currentDir w
@[export omega_test_path_process_cwd] public def pathProcessCwd (w : PathWorld) := Omega.IO.Process.getCurrentDir w
@[export omega_test_path_real] public def pathReal (p : Omega.String) (w : PathWorld) := Omega.IO.FS.realPath ⟨p⟩ w
@[export omega_test_path_temp_dir] public def pathTempDir (w : PathWorld) := Omega.IO.FS.createTempDir w
@[export omega_test_path_app] public def pathApp (w : PathWorld) := Omega.IO.appPath w
@[export omega_test_path_list] public def pathList (p : Omega.String) (w : PathWorld) :=
  Omega.System.FilePath.readDir ⟨p⟩ w

@[export omega_test_open] public def fileOpen (p : Omega.String) (w : PathWorld) :=
  Omega.IO.FS.Handle.mk ⟨p⟩ .readWrite w
@[export omega_test_tty] public def fileTty (h : Omega.IO.FS.Handle) (w : PathWorld) := h.isTty w
@[export omega_test_flush] public def fileFlush (h : Omega.IO.FS.Handle) (w : PathWorld) := observe (h.flush w)
@[export omega_test_rewind] public def fileRewind (h : Omega.IO.FS.Handle) (w : PathWorld) := observe (h.rewind w)
@[export omega_test_truncate] public def fileTruncate (h : Omega.IO.FS.Handle) (w : PathWorld) := observe (h.truncate w)
@[export omega_test_unlock] public def fileUnlock (h : Omega.IO.FS.Handle) (w : PathWorld) := observe (h.unlock w)
@[export omega_test_lock] public def fileLock (h : Omega.IO.FS.Handle) (w : PathWorld) := observe (h.lock .true w)
@[export omega_test_try_lock] public def fileTryLock (h : Omega.IO.FS.Handle) (w : PathWorld) := h.tryLock .true w
@[export omega_test_read] public def fileRead (h : Omega.IO.FS.Handle) (n : Omega.USize) (w : PathWorld) := h.read n w
@[export omega_test_write] public def fileWrite (h : Omega.IO.FS.Handle) (buf : Omega.ByteArray) (w : PathWorld) :=
  observe (h.write buf w)
@[export omega_test_line] public def fileLine (h : Omega.IO.FS.Handle) (w : PathWorld) := h.getLine w
@[export omega_test_put] public def filePut (h : Omega.IO.FS.Handle) (s : Omega.String) (w : PathWorld) :=
  observe (h.putStr s w)
