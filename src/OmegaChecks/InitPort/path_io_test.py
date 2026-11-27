"""Run filesystem and environment consumers against isolated UTF-8 fixtures."""
import os
from pathlib import Path
import sysconfig

from generated_native import HERE, STRICT_SOURCES, run


def check_paths(stage, library, path_object, io_object, check_read_into=False):
    test = stage / "path-io-check"
    test.mkdir()
    source = test / "consumer.c"
    run("lean", "-R", STRICT_SOURCES, "-c", source, "-o", test / "PathIOConsumer.olean", STRICT_SOURCES / "PathIOConsumer.lean",
        env={**os.environ, "LEAN_PATH": str(library)})
    native = test / "consumer"
    flags = ["-DOMEGA_TEST_READ_INTO"] if check_read_into else []
    run("leanc", *flags, "-I", HERE, source, path_object, *([io_object] if io_object.is_file() else []),
        HERE / "consumers" / "path_io_consumer.c", "-o", native)
    shim_c = test / "extern.c"
    run("lake", "env", "lean", "--run", HERE / "PathIONative.lean", "--interpreter", library, shim_c)
    shim = test / ("extern" + (sysconfig.get_config_var("SHLIB_SUFFIX") or ".so"))
    run("leanc", "-shared", "-fPIC", "-DLEAN_EXPORTING", "-I", HERE, shim_c, "-o", shim)
    commands = ([native], ["lake", "env", "lean", "--load-dynlib=" + str(shim), "--run",
                            HERE / "consumers" / "PathIOIRConsumer.lean", library, test])
    env = {**os.environ, "OMEGA_PATH_TEST_VALUE": "héλ界"}
    env.pop("OMEGA_PATH_TEST_ABSENT", None)
    for i, command in enumerate(commands):
        root = test / str(i)
        root.mkdir()
        paths = [root / "旧-λ", root / "新-é", root / "文件", root / "链接", root]
        paths[2].write_bytes(b"fixture")
        run(*command, *paths, env=env)
        if any(root.iterdir()):
            raise ValueError("path consumer left a directory or file behind")
