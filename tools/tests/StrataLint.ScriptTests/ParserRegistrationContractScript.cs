namespace StrataLint.Tests;

internal static class ParserRegistrationContractScript
{
    internal static string Source => SourceContextContractScript.Source.Replace(
        "if __name__ == \"__main__\":", "if False:", StringComparison.Ordinal) + "\n" + """"
    HEADER = ("/- GID: D5/S0/Carrier/Anonymous\n"
              "   generality: G\n   mirror-B: none(waiver:test-fixture)\n"
              "   mirror-E: none(waiver:test-fixture)\n   anchors: []\n   utility: none\n"
              "   digest: Anonymous source admission fixture. -/\n")

    def registry_assertion(expected):
        # This is a compiler probe ONLY. Never pass it to query/source projection.
        return ("open Lean Elab Command in\nrun_cmd do\n"
                '  unless ((Lean.Parser.getTokenTable (← getEnv)).find? "=\'").isSome == '
                + str(expected).lower() + ' do\n    throwError "TOKEN_REGISTRY_MISMATCH"\n')

    def assert_result(result, expected):
        contract.assertIsNone(result["error"])
        contract.assertEqual(expected, result["commands"][-1]["equality"])
        contract.assertEqual(0, result["projectedDeclarations"])
        contract.assertEqual(0, result["elaboratedDeclarations"])

    ProducerContract.setUpClass()
    try:
        contract = ProducerContract()
        operation = sys.argv[1]
        output = {}
        if operation == "witness":
            wrapped, mode = sys.argv[2] == "True", sys.argv[3]
            source = (HEADER + "import Lean\nnamespace Registration\n"
                      'infix:50 " =\' " => Eq' + (" in" if wrapped else "") + "\n"
                      "example : True := by trivial\nend Registration\nexample : True := by decide\n")
            contract.compile_source(source)
            contract.compile_source(source + registry_assertion(True))
            output = dict(source=source, result=contract.query(source, mode))
        elif operation == "separator":
            parser = sys.argv[2]
            # An explicit parser owns tokens; metadata is used only when it is absent.
            declarations = [
                (f'syntax "eqList" {parser}(term, "=\'", ",") : term', False),
                (f'syntax "eqList" {parser}(term, ",", ",") : term', False),
                (f'syntax "eqList" {parser}(term, ",", "=\'") : term', True),
                (f'syntax "eqList" {parser}(term, "=\'") : term', True),
                (f'syntax "eqList" {parser}(term, "=\'", (","), allowTrailingSep) : term', False),
                (f'syntax "eqList" {parser}(term, "=\'", unicode("comma", ",")) : term', False),
                (f'macro "eqList" xs:{parser}(term, "=\'", ",") : term => `(True)', False),
                (f'elab "eqList" xs:{parser}(term, "=\'", ",") : term => return Lean.mkConst ``True', False),
            ]
            for declaration, registered in declarations:
                source = "import Lean\n" + declaration + "\nexample : True := by decide\n"
                contract.compile_source(source)
                contract.compile_source(source + registry_assertion(registered))
                managed = [dict(module="D5.Registration", path="D5/Registration.lean", source=source)]
                # Bound each compiler process to one source and its three contexts.
                requests = []
                for mode in ["current", "projected", "source"]:
                    query = source if mode == "current" else "import D5.Registration\nexample : True := by decide\n"
                    requests.append(request_for(query, mode, managed))
                results = contract.query_requests(requests)
                print("SEPARATOR_PROJECTION " + json.dumps(results), flush=True)
                for result in results:
                    assert_result(result, registered)
        elif operation == "locality":
            locality, second = sys.argv[2], sys.argv[3] == "True"
            declaration = locality + 'infix:50 " =\' " => Eq\n'
            wrapper = ("set_option pp.unicode.fun true in\n" + declaration if second else
                       declaration.rstrip() + " in\nexample : True := by trivial\n")
            marker = "example : True := by decide\n"
            source = ("import Lean\nnamespace Registration\n" + wrapper + marker
                      + "end Registration\n" + marker + "open scoped Registration\n" + marker)
            expected = [second or locality != "local ", not locality, locality != "local "]
            contract.compile_source(source)
            probe = source
            for value in expected:
                probe = probe.replace(marker, registry_assertion(value), 1)
            contract.compile_source(probe)
            for mode in ["current", "source"]:
                result = contract.query(source, mode)
                print("WRAPPER_LOCALITY " + json.dumps(dict(source=source, mode=mode, result=result)), flush=True)
                contract.assertIsNone(result["error"])
                examples = [row for row in result["commands"] if row["kind"] == "Lean.Parser.Command.declaration"]
                contract.assertEqual(expected, [row["equality"] for row in examples])
            managed = [dict(module="D5.Registration", path="D5/Registration.lean", source=source)]
            query = "import D5.Registration\nexample : True := by decide\nopen scoped Registration\nexample : True := by decide\n"
            for mode in ["projected", "source"]:
                result = contract.query(query, mode, managed)
                contract.assertIsNone(result["error"])
                contract.assertEqual([not locality, locality != "local "],
                    [row["equality"] for row in result["commands"] if row["kind"] == "Lean.Parser.Command.declaration"])
        elif operation == "nonexecution":
            source = ("import Lean\nnamespace Registration\n"
                      "set_option pp.unicode.fun true in\n"
                      'infix:50 " =\' " => protectedExpansionMustNeverExecute in\n'
                      "theorem protectedTarget : True := by exact protectedProofMustNeverExecute\n"
                      "attribute [local simp] protectedTarget in\n"
                      "attribute [local instance] protectedInstanceMustNeverResolve\nend Registration\n")
            managed = [dict(module="D5.Registration", path="D5/Registration.lean", source=source)]
            query = "import D5.Registration\nexample : True := by decide\n"
            for mode in ["projected", "source"]:
                assert_result(contract.query(query, mode, managed), True)
        elif operation == "unknown":
            for command in ["attribute [term_parser] Lean.Parser.Term.paren",
                            "run_cmd pure ()", "initialize pure ()"]:
                source = "import Lean\nset_option pp.unicode.fun true in\n" + command + "\n"
                contract.compile_source(source)
                for mode in ["current", "source"]:
                    result = contract.query(source, mode)
                    contract.assertIsNotNone(result["error"])
                    contract.assertEqual(3, result["error"]["line"])
        elif operation == "extractor":
            wrapped = sys.argv[2] == "True"
            source = ("import Lean\nnamespace Registration\n"
                      'infix:50 " =\' " => Eq' + (" in" if wrapped else "") + "\n"
                      "theorem kept : True := by trivial\nend Registration\n")
            contract.compile_source(source)
            output = dict(source=source, result=contract.query(source))
        else:
            raise AssertionError("unknown contract operation: " + operation)
        print("PARSER_REGISTRATION_RESULT " + json.dumps(output), flush=True)
    finally:
        ProducerContract.tearDownClass()
    """";
}
