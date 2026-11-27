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
