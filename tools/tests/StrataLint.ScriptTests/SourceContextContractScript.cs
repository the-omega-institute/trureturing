namespace StrataLint.Tests;

internal static class SourceContextContractScript
{
    internal const string Source = """"
    """Compiler differential contract. Run in a canonically warmed candidate tree."""
    import json
    import importlib.util
    import os
    from pathlib import Path
    import subprocess
    import sys
    import tempfile
    import unittest

    REPOSITORY = Path(sys.argv.pop(1))
    SOURCE_PACKET = REPOSITORY / "tools/tests/StrataLint.ScriptTests/Fixtures/SourceContext/sources.json"
    FIXTURES = None
    PRODUCER = REPOSITORY / "tools/lean-inspector/SourceContext.lean"


    def init_char_source(namespace):
        return (f"import Init\nnamespace {namespace}\ndef g' : Nat := 0\n"
                f"end {namespace}\nopen {namespace}\nexample : ')' =')' := by decide\n")


    def request_for(source, mode="current", managed=(), source_modules=()):
        return dict(mode=mode, source=source, path="D5/Query.lean", module="D5.Query",
                    managed=list(managed), options=[], sourceModules=list(source_modules))


    class ProducerContract(unittest.TestCase):
        @classmethod
        def setUpClass(cls):
            cls.scratch = tempfile.TemporaryDirectory(prefix="source-context-contract-")
            cls.root = Path(cls.scratch.name)
            global FIXTURES
            FIXTURES = cls.root / "fixtures"
            for relative, source in json.loads(SOURCE_PACKET.read_text()).items():
                path = FIXTURES / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            cls.env = dict(os.environ)
            search = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=REPOSITORY,
                                    text=True, capture_output=True, check=True).stdout.strip()
            cls.env["LEAN_PATH"] = str(cls.root) + os.pathsep + search
            cls.lean = subprocess.run(["lake", "env", "which", "lean"], cwd=REPOSITORY,
                                      text=True, capture_output=True, check=True).stdout.strip()
            spec = importlib.util.spec_from_file_location("source_context", PRODUCER.with_name("source-context.py"))
            production = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(production)
            preparation = production.Preparation(REPOSITORY, None, None, cls.root, "lake")
            cls.query_command, cls.query_environment = preparation.compiler_query(PRODUCER)
            # The fixture's compiled D5 modules precede the current repository's D5
            # directory, exactly as they did in the direct compiler control.
            cls.query_command = [cls.lean, "--run", cls.query_command[-1]]
            cls.query_environment["LEAN_PATH"] += os.pathsep + cls.env["LEAN_PATH"]

        @classmethod
        def import_fixtures(cls):
            sources = sorted((FIXTURES / "e2/D5").rglob("*.lean"))
            sources.sort(key=lambda p: p.stem == "Two")
            return sources

        @classmethod
        def compile_import_fixtures(cls, sources=None):
            sources = cls.import_fixtures() if sources is None else sources
            for path in sources:
                output = cls.root / path.relative_to(FIXTURES / "e2").with_suffix(".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                result = subprocess.run([cls.lean, "-R", str(FIXTURES / "e2"), "-o", str(output), str(path)],
                                        cwd=REPOSITORY, env=cls.env, text=True, capture_output=True)
                if result.returncode:
                    raise AssertionError(f"fixture compilation: {path}\n{result.stdout}\n{result.stderr}")

        @classmethod
        def tearDownClass(cls):
            cls.scratch.cleanup()

        def query(self, source, mode="current", managed=(), source_modules=()):
            return self.query_requests(request_for(source, mode, managed, source_modules))

        def query_requests(self, request):
            path = self.root / "request.json"
            path.write_text(json.dumps(request))
            result = subprocess.run(self.query_command + [str(path), str(self.root / "query")],
                                    cwd=REPOSITORY, env=self.query_environment, text=True, capture_output=True)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            decoded = json.loads(result.stdout)
            self.assertIsInstance(decoded, list if isinstance(request, list) else dict)
            if isinstance(request, list):
                self.assertEqual(len(request), len(decoded))
            return decoded

        def test_import_visibility_matches_actual_importer(self, selected=None):
            if selected is None:
                self.compile_import_fixtures()
            managed = [{"module": str(p.relative_to(FIXTURES / "e2").with_suffix("")).replace("/", "."),
                        "path": str(p.relative_to(FIXTURES / "e2")), "source": p.read_text()}
                       for p in sorted((FIXTURES / "e2/D5").rglob("*.lean"))]
            rows = list(sorted((FIXTURES / "e2/Rows").glob("*.lean")))
            rows += [None]
            if selected is not None:
                rows = rows[selected:selected + 1]
            requests = []
            for path in rows:
                source = path.read_text() if path else (
                    "module\nimport D5.S0.Carrier.Private\npublic import D5.S0.Carrier.Public\n")
                for mode in ["current", "projected"]:
                    requests.append(dict(mode=mode, source=source, path="D5/Query.lean", options=[], managed=managed))
            results = self.query_requests(requests)
            for index, path in enumerate(rows):
                label = path.stem if path else "RepeatedPrivatePublic"
                with self.subTest(label=label):
                    actual, projected = results[index * 2:index * 2 + 2]
                    self.assertIsNone(actual["error"])
                    self.assertIsNone(projected["error"])
                    self.assertEqual(actual["initialEquality"], projected["initialEquality"])
                    self.assertEqual(actual["openedEquality"], projected["openedEquality"])
                    self.assertEqual(actual["imports"], projected["imports"])
                    self.assertEqual(0, projected["projectedDeclarations"])

        def test_command_boundaries_and_scopes(self):
            counts = {"Indented": 7, "OpenIn": 3, "ProofA": 2, "ProofB": 2,
                      "Quoted": 4, "Shadow": 7}
            results = self.query_requests([request_for((FIXTURES / "e3" / (label + ".lean")).read_text())
                                           for label in counts])
            for (label, count), result in zip(counts.items(), results):
                with self.subTest(label=label):
                    self.assertIsNone(result["error"])
                    self.assertEqual(count, len(result["commands"]))
                    self.assertEqual(0, result["elaboratedDeclarations"])
                    if label in ["ProofA", "ProofB", "Shadow", "Quoted"]:
                        self.assertFalse(result["commands"][-1]["equality"])
            result = results[list(counts).index("OpenIn")]
            wrapper = result["commands"][1]
            self.assertFalse(wrapper["equality"])
            self.assertTrue(wrapper["children"][0]["equality"])
            self.assertFalse(result["commands"][2]["equality"])

        def test_errors_are_immediate_and_sticky(self):
            labels = ["InvalidProof", "ShadowRoot"]
            results = self.query_requests([request_for((FIXTURES / "e3" / (label + ".lean")).read_text()) for label in labels])
            for label, result in zip(labels, results):
                with self.subTest(label=label):
                    self.assertIsNotNone(result["error"])
                    self.assertGreater(result["error"]["line"], 0)

        def test_option_wrapper_preserves_nested_command_scope(self):
            result = self.query("import Mathlib.ModelTheory.Syntax\n"
                                "set_option pp.unicode.fun true in\n"
                                "open FirstOrder in\n"
                                "theorem query : 'g' ='g' := by rfl\n"
                                "theorem following : 'g' = 'g' := by rfl\n")
            self.assertIsNone(result["error"])
            self.assertEqual(2, len(result["commands"]))
            wrapper = result["commands"][0]
            self.assertEqual("Lean.Parser.Command.in", wrapper["kind"])
            inner = wrapper["children"][0]
            self.assertFalse(inner["equality"])
            self.assertTrue(inner["children"][0]["equality"])
            self.assertFalse(result["commands"][1]["equality"])

        def test_init_namespace_does_not_create_registration(self):
            namespaces = ["FirstOrder", "Ordinary"]
            results = self.query_requests([request_for(init_char_source(ns)) for ns in namespaces])
            for namespace, result in zip(namespaces, results):
                with self.subTest(namespace=namespace):
                    self.assertIsNone(result["error"])
                    self.assertFalse(result["commands"][-1]["equality"])

        def test_simp_attributes_do_not_elaborate_targets_or_change_tokens(self):
            attributes = ["simp", "local simp", "scoped simp", "-simp", "simp, local simp", "simp 100"]
            requests = []
            for attribute in attributes:
                # A declaration-free projection must not elaborate this protected proof,
                # nor resolve its local theorem when interpreting the attribute effect.
                source = ("import Init\nnamespace AttrScope\n"
                          "theorem attr_control : True := by exact protectedProofMustNeverExecute\n"
                          f"attribute [{attribute}] attr_control\nend AttrScope\n")
                query = "import D5.AttrSource\nexample : ')' =')' := by decide\n"
                requests.append(request_for(query, "projected", managed=[dict(
                    module="D5.AttrSource", path="D5/AttrSource.lean", source=source)]))
            results = self.query_requests(requests)
            for attribute, result in zip(attributes, results):
                with self.subTest(attribute=attribute):
                    self.assertIsNone(result["error"])
                    self.assertFalse(result["initialEquality"])
                    self.assertFalse(result["commands"][-1]["equality"])
                    self.assertEqual(0, result["projectedDeclarations"])
                    self.assertEqual(0, result["elaboratedDeclarations"])

        def test_unmodeled_attribute_is_a_located_error(self):
            # term_parser is a real current-Lean registration handler. Mixing it
            # with simp must not turn the entire attribute list into a known no-op.
            for attribute in ["term_parser", "simp, term_parser", "instance, term_parser", "-term_parser"]:
                result = self.query("import Lean\n"
                                    f"attribute [{attribute}] Lean.Parser.Term.paren\n"
                                    "example : ')' =')' := by decide\n")
                self.assertIsNotNone(result["error"])
                self.assertEqual(2, result["error"]["line"])
                self.assertIn("cannot determine this attribute registration effect", result["error"]["message"])

        def compile_source(self, source):
            path = self.root / "Registration.lean"
            path.write_text(source)
            result = subprocess.run([self.lean, str(path)], cwd=REPOSITORY, env=self.env,
                                    text=True, capture_output=True)
            print("REGISTRATION_COMPILER " + json.dumps(dict(source=source, exit=result.returncode,
                  stdout=result.stdout, stderr=result.stderr)), flush=True)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)

        def test_notation_expansion_strings_do_not_register_tokens(self):
            declarations = [
                'notation "attrWitness" => "=\'"',
                'notation "attrWitness" => "safe"',
                'prefix:50 "attrWitness" => fun (_ : Nat) => "=\'"',
                'macro "attrWitness" : term => `("=\'")',
                'elab "attrWitness" : term => return Lean.mkStrLit "=\'"',
            ]
            sources = ["import Lean\n" + declaration + "\nexample : ')' =')' := by decide\n"
                       for declaration in declarations]
            for source in sources:
                self.compile_source(source)
            requests = []
            for source in sources:
                requests.append(request_for(source))
                managed = [dict(module="D5.Registration", path="D5/Registration.lean", source=source)]
                query = "import D5.Registration\nexample : ')' =')' := by decide\n"
                requests.append(request_for(query, "projected", managed=managed))
                requests.append(request_for(query, "source", managed=managed))
            results = self.query_requests(requests)
            print("REGISTRATION_PROJECTION " + json.dumps(results), flush=True)
            for index, result in enumerate(results):
                with self.subTest(declaration=declarations[index // 3], mode=requests[index]["mode"]):
                    self.assertIsNone(result["error"])
                    self.assertFalse(result["commands"][-1]["equality"])
                    self.assertEqual(0, result["elaboratedDeclarations"])

        def test_declaration_tokens_retain_compiler_locality(self):
            declarations = ['notation "=\'" => Eq', 'infix:50 "=\'" => Eq',
                            'syntax "=\'" : term', 'syntax unicode("eqUnicode", "=\'") : term',
                            'syntax "eqList" sepBy1(term, "=\'") : term']
            for declaration in declarations:
                for locality in ["", "local ", "scoped "]:
                    source = ("import Lean\nnamespace Registration\n" + locality + declaration
                              + "\nexample : True := by trivial\nend Registration\n"
                              "example : True := by trivial\nopen scoped Registration\n"
                              "example : True := by trivial\n")
                    self.compile_source(source)
                    result = self.query(source)
                    print("REGISTRATION_LOCALITY " + json.dumps(dict(source=source, result=result)), flush=True)
                    self.assertIsNone(result["error"])
                    self.assertEqual(7, len(result["commands"]))
                    examples = [result["commands"][index] for index in [2, 4, 6]]
                    self.assertEqual([True, not locality, locality != "local "],
                                     [row["equality"] for row in examples])

        def test_instance_attributes_do_not_elaborate_targets_or_change_tokens(self):
            attributes = ["instance", "local instance", "scoped instance", "-instance",
                          "instance 100", "local instance 100", "scoped instance 100"]
            requests = []
            for attribute in attributes:
                source = ("import Init\nnamespace AttrScope\n"
                          "@[instance] def attr_instance : Inhabited Unit := ⟨()⟩\n"
                          f"attribute [{attribute}] attr_instance\nend AttrScope\n"
                          "example : ')' =')' := by decide\n")
                self.compile_source(source)
                requests.append(request_for(source))
                # This second input is deliberately not a compiling-source witness:
                # resolving or evaluating its source-only target must fail.
                protected = source.replace("⟨()⟩", "by exact protectedTargetMustNeverExecute")
                managed = [dict(module="D5.AttrSource", path="D5/AttrSource.lean", source=protected)]
                query = "import D5.AttrSource\nexample : ')' =')' := by decide\n"
                requests.append(request_for(query, "projected", managed=managed))
                requests.append(request_for(query, "source", managed=managed))
            results = self.query_requests(requests)
            print("INSTANCE_PROJECTION " + json.dumps(results), flush=True)
            for index, result in enumerate(results):
                with self.subTest(attribute=attributes[index // 3], mode=requests[index]["mode"]):
                    self.assertIsNone(result["error"])
                    self.assertFalse(result["initialEquality"])
                    self.assertFalse(result["commands"][-1]["equality"])
                    self.assertEqual(0, result["projectedDeclarations"])
                    self.assertEqual(0, result["elaboratedDeclarations"])

        def test_registration_source_is_data_and_scope_is_measured(self):
            external = self.root / "ProbeExternal/Equality.lean"
            external.parent.mkdir(parents=True, exist_ok=True)
            external.write_text("import Init\nnamespace EqScope\nend EqScope\n")
            compiled = subprocess.run([self.lean, "-R", str(self.root), "-o",
                                       str(external.with_suffix(".olean")), str(external)],
                                      cwd=REPOSITORY, env=self.env, text=True, capture_output=True)
            self.assertEqual(0, compiled.returncode, compiled.stdout + compiled.stderr)
            query = ("import ProbeExternal.Equality\nopen scoped EqScope\n"
                     "example : 'g' ='g' := by rfl\n")
            alternatives = [("", True), ("scoped ", True), ("local ", False)]
            requests = []
            for modifier, _ in alternatives:
                old = "import Init\nnamespace EqScope\n" + modifier + (
                    'infix:50 " =\' " => ThisOldExpansionMustNeverBeElaborated\nend EqScope\n')
                requests.append(request_for(query, "source", source_modules=[{
                    "module": "ProbeExternal.Equality", "path": "ProbeExternal/Equality.lean", "source": old}]))
            results = self.query_requests(requests + [request_for(query)])
            for (modifier, expected), result in zip(alternatives, results):
                with self.subTest(modifier=modifier):
                    self.assertIsNone(result["error"])
                    self.assertEqual(expected, result["commands"][-1]["equality"])
                    self.assertEqual(0, result["projectedDeclarations"])
            self.assertFalse(results[-1]["commands"][-1]["equality"])


    class PreparationContract(unittest.TestCase):
        def test_failed_compiler_is_not_a_cached_context(self):
            spec = importlib.util.spec_from_file_location("source_context", PRODUCER.with_name("source-context.py"))
            production = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(production)
            with tempfile.TemporaryDirectory(prefix="source-process-contract-") as temporary:
                preparation = production.Preparation(REPOSITORY, None, None, Path(temporary), "absent-current-lake")
                request = dict(kind="commands", module="D5.Query", side="current", path="D5/Query.lean",
                               sourceSha256="a", producerSha256="b", configurationSha256="c", graphSha256="d",
                               referenceConfigurationSha256="e", managed=[])
                with self.assertRaises(FileNotFoundError):
                    preparation.produce(request)

        def test_duplicate_package_module_is_unknown(self):
            spec = importlib.util.spec_from_file_location("source_context", PRODUCER.with_name("source-context.py"))
            production = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(production)
            with tempfile.TemporaryDirectory(prefix="source-origin-contract-") as temporary:
                root = Path(temporary)
                packages = []
                for name in ["first", "second"]:
                    package = root / ".lake/packages" / name
                    package.mkdir(parents=True)
                    (package / "Shared.lean").write_text("import Init\n")
                    for args in [["init", "--quiet"], ["add", "."], ["-c", "user.name=Source Fixture",
                                 "-c", "user.email=source@example.invalid", "commit", "--quiet", "--no-gpg-sign", "-m", "source"]]:
                        subprocess.run(["git"] + args, cwd=package, check=True, capture_output=True)
                    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=package, text=True).strip()
                    packages.append(dict(name=name, type="git", rev=revision, url=package.as_uri()))
                preparation = production.Preparation(root, None, None, root, "lake")
                self.assertEqual("first", preparation.external_source("Shared", packages[:1])["package"])
                with self.assertRaisesRegex(RuntimeError, "ambiguous"):
                    preparation.external_source("Shared", packages)


    if __name__ == "__main__":
        if sys.argv[1:2] == ["--prepare-import-contract"]:
            ProducerContract.setUpClass()
            # Move the run-local compiler outputs into the caller-owned test lifetime.
            # Its compiled artifacts and environment are used only by this test.
            import shutil
            target = Path(sys.argv[2])
            old_root = str(ProducerContract.root)
            shutil.copytree(ProducerContract.root, target, dirs_exist_ok=True)
            data = dict(command=ProducerContract.query_command, environment=ProducerContract.query_environment,
                        lean=ProducerContract.lean, env=ProducerContract.env)
            (target / "compiler.json").write_text(json.dumps(data).replace(old_root, str(target)))
            print(json.dumps(dict(sources=[str(p).replace(old_root, str(target)) for p in ProducerContract.import_fixtures()],
                                  comparisons=len(list((FIXTURES / "e2/Rows").glob("*.lean"))) + 1)))
            ProducerContract.tearDownClass()
        elif sys.argv[1:2] in (["--compile-import"], ["--check-import"]):
            ProducerContract.root = Path(sys.argv[2])
            FIXTURES = ProducerContract.root / "fixtures"
            data = json.loads((ProducerContract.root / "compiler.json").read_text())
            ProducerContract.query_command, ProducerContract.query_environment = data["command"], data["environment"]
            ProducerContract.lean, ProducerContract.env = data["lean"], data["env"]
            if sys.argv[1] == "--compile-import":
                ProducerContract.compile_import_fixtures([Path(sys.argv[3])])
            else:
                ProducerContract().test_import_visibility_matches_actual_importer(int(sys.argv[3]))
        elif sys.argv[1:2] == ["--options"]:
            spec = importlib.util.spec_from_file_location("source_context", PRODUCER.with_name("source-context.py"))
            production = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(production)
            with tempfile.TemporaryDirectory(prefix="source-options-contract-") as temporary:
                preparation = production.Preparation(REPOSITORY, None, None, Path(temporary), "lake")
                command, environment = preparation.compiler_query(PRODUCER.with_name("SourceOptions.lean"))
                result = subprocess.run(command + sys.argv[2:], cwd=REPOSITORY, env=environment,
                                        text=True, capture_output=True)
                sys.stdout.write(result.stdout)
                sys.stderr.write(result.stderr)
                raise SystemExit(result.returncode)
        elif sys.argv[1:] == ["--init-contexts"]:
            ProducerContract.setUpClass()
            try:
                contract = ProducerContract()
                sources = [init_char_source(namespace) for namespace in ["FirstOrder", "Ordinary"]]
                results = contract.query_requests([request_for(source) for source in sources])
                print(json.dumps([dict(source=source, result=result) for source, result in zip(sources, results)]))
            finally:
                ProducerContract.tearDownClass()
        else:
            unittest.main(verbosity=2)

    """";
}
