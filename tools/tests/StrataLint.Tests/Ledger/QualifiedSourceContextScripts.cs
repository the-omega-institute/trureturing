namespace StrataLint.Tests;

internal static class QualifiedSourceContextScripts
{
    internal const string ContextProducer = """"
    """Current compiler contexts for truthful declaration/material fixtures.

    Each caller-guarded operation uses the same run-local compiler and current imports.
    Protected helpers and registration source are declaration-free query metadata.
    """
    import importlib.util
    import json
    import os
    from pathlib import Path
    import subprocess
    import sys

    REPOSITORY = Path(sys.argv.pop(1))
    FIXTURES = REPOSITORY / "tools/tests/StrataLint.Tests/Ledger/Fixtures/ContextQualification"
    SOURCES = json.loads((FIXTURES / "sources.json").read_text())


    def requests(before, after):
        external = dict(module="ProbeExternal.Equality", path="ProbeExternal/Equality.lean",
                        source=SOURCES[before + "/ProbeExternal/Equality.lean"])
        rows = []
        for side, case in [("current", after), ("protected", before)]:
            helper_path = "D5/S0/Carrier/Helper.lean"
            helper = dict(module="D5.S0.Carrier.Helper", path=helper_path,
                          source=SOURCES[case + "/" + helper_path])
            for path in ["D5/S0/Carrier/A.lean", helper_path]:
                for kind in ["commands", "registration"]:
                    request = dict(mode="source" if kind == "registration" else
                        "current" if side == "current" else "projected", path=path,
                        module=path[:-5].replace("/", "."), source=SOURCES[case + "/" + path],
                        managed=[helper] if path != helper_path else [], sourceModules=[external], options=[])
                    rows.append((dict(side=side, path=path, kind=kind), request))
        return external, rows


    def main():
        before, after, directory, operation, *arguments = sys.argv[1:]
        root = Path(directory)
        metadata = root / "compiler.json"
        if operation == "prepare":
            lean = subprocess.run(["lake", "env", "which", "lean"], cwd=REPOSITORY,
                                  text=True, capture_output=True, check=True).stdout.strip()
            search = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=REPOSITORY,
                                    text=True, capture_output=True, check=True).stdout.strip()
            spec = importlib.util.spec_from_file_location("source_context",
                REPOSITORY / "tools/lean-inspector/source-context.py")
            production = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(production)
            preparation = production.Preparation(REPOSITORY, None, None, root, "lake")
            command, environment = preparation.compiler_query(REPOSITORY / "tools/lean-inspector/SourceContext.lean")
            environment["LEAN_PATH"] += os.pathsep + str(root) + os.pathsep + search
            metadata.write_text(json.dumps(dict(lean=lean, command=[lean] + command[3:], environment=environment)))
            external, rows = requests(before, after)
            print(json.dumps(dict(external=external, count=len(rows))))
            return
        data = json.loads(metadata.read_text())
        if operation == "compile":
            relative = arguments[0]
            source = root / "current" / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(SOURCES[after + "/" + relative])
            target = root / Path(relative).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run([data["lean"], "-R", str(root / "current"), "-o", str(target),
                            str(source)], cwd=REPOSITORY, env=data["environment"], check=True)
            return
        if operation != "query":
            raise ValueError("unknown fixture operation: " + operation)
        key, request = requests(before, after)[1][int(arguments[0])]
        request_file = root / "request.json"
        request_file.write_text(json.dumps(request))
        result = subprocess.run(data["command"] + [str(request_file), str(root / "query")], cwd=REPOSITORY,
                                env=data["environment"], text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        row = json.loads(result.stdout)
        assert row.get("error") is None, (key, row)
        print(json.dumps(dict(key, result=row)))


    if __name__ == "__main__":
        main()

    """";
    internal const string Preparation = """"
    """Exercise the actual preparation loop with an isolated Git/source fixture.

    The compiler and Lake environment are the canonically warmed current checkout.
    Only these fixtures' current imports are compiled into its additional search path.
    Demand, immutable source acquisition, binding, verification and publication use
    the production implementation. No protected body or old package code executes.
    """
    import importlib.util
    import os
    from pathlib import Path
    import subprocess
    import sys

    compiler, repository, report, baseline, mode, *arguments = sys.argv[1:]
    compiler, repository = Path(compiler), Path(repository)
    lean, search = None, ""
    script = compiler / "tools/lean-inspector/source-context.py"
    spec = importlib.util.spec_from_file_location("source_context", script)
    production = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(production)

    library = repository / ".lake/build/lib/lean"
    os.environ["LEAN_PATH"] = str(library) + os.pathsep + os.environ.get("LEAN_PATH", "")
    if mode == "compile":
        lean = subprocess.run(["lake", "env", "which", "lean"], cwd=compiler,
                              text=True, capture_output=True, check=True).stdout.strip()
        search = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=compiler,
                                text=True, capture_output=True, check=True).stdout.strip()
        relative = arguments[0]
        target = library / Path(relative).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([lean, "-R", str(repository), "-o", str(target), str(repository / relative)],
                       cwd=compiler, check=True)
        raise SystemExit(0)

    original_init = production.Preparation.__init__
    original_query = production.Preparation.query
    original_options = production.Preparation.current_options
    original_compiler_query = production.Preparation.compiler_query


    def initialize(self, *args):
        original_init(self, *args)
        self.cli = compiler / "tools/StrataLint.Cli/StrataLint.Cli.csproj"


    def current_compiler(self, operation, argument):
        root = self.repository
        try:
            self.repository = compiler
            return operation(self, argument)
        finally:
            self.repository = root


    production.Preparation.__init__ = initialize
    production.Preparation.query = lambda self, request: current_compiler(self, original_query, request)
    production.Preparation.current_options = lambda self, module: current_compiler(self, original_options, module)


    def fixture_compiler_query(self, source):
        global lean, search
        if lean is None:
            lean = subprocess.run(["lake", "env", "which", "lean"], cwd=compiler,
                                  text=True, capture_output=True, check=True).stdout.strip()
            search = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=compiler,
                                    text=True, capture_output=True, check=True).stdout.strip()
        command, environment = original_compiler_query(self, source)
        environment = dict(environment)
        environment["LEAN_PATH"] += os.pathsep + search
        return [lean] + command[3:], environment


    production.Preparation.compiler_query = fixture_compiler_query
    sys.argv = [str(script), "--repository", str(repository), "--report", report, "--base", baseline]
    if mode == "offline":
        sys.argv.append("--verify")
    production.main()

    """";
}
