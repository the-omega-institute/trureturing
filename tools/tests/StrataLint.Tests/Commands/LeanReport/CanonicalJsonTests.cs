using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CanonicalJsonTests
{
    private const string EquivalenceProbe = """
        import importlib.util
        import pathlib
        import sys

        spec = importlib.util.spec_from_file_location("materials", pathlib.Path(sys.argv[1]))
        materials = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(materials)

        # Fixed bytes are independent of both json.dumps and the production
        # scalar escaper, including separator spaces and the terminal LF.
        fixtures = {
            "bmp": [
                ("", b'""\n'), ({}, b'{}\n'), ([], b'[]\n'), ("ASCII", b'"ASCII"\n'),
                ("\u4e2d\u6587 \u03b1\u03b2\u03b3 e\u0301",
                 b'"\xe4\xb8\xad\xe6\x96\x87 \xce\xb1\xce\xb2\xce\xb3 e\xcc\x81"\n'),
                ("".join(map(chr, range(0x20))),
                 b'"\\u0000\\u0001\\u0002\\u0003\\u0004\\u0005\\u0006\\u0007'
                 b'\\b\\t\\n\\u000b\\f\\r\\u000e\\u000f\\u0010\\u0011\\u0012\\u0013'
                 b'\\u0014\\u0015\\u0016\\u0017\\u0018\\u0019\\u001a\\u001b'
                 b'\\u001c\\u001d\\u001e\\u001f"\n'),
                ('quote=" slash=\\ newline=\n tab=\t',
                 b'"quote=\\" slash=\\\\ newline=\\n tab=\\t"\n'),
                ({"z": [3, {"b": False, "a": None}], "a": {"empty": ""}},
                 b'{"a": {"empty": ""}, "z": [3, {"a": null, "b": false}]}\n'),
            ],
            "supplementary": [
                ("emoji \U0001F600", b'"emoji \\uD83D\\uDE00"\n'),
                ("CJK-B \U00020000", b'"CJK-B \\uD840\\uDC00"\n'),
                ({"\U0001F680": ["mixed \u4e2d\U0001F642", "\U00020000"]},
                 b'{"\\uD83D\\uDE80": ["mixed \xe4\xb8\xad\\uD83D\\uDE42", "\\uD840\\uDC00"]}\n'),
                ({"\U00010000": 3, "\uFFFF": 2, "a": 1},
                 b'{"a": 1, "\xef\xbf\xbf": 2, "\\uD800\\uDC00": 3}\n'),
            ],
            "boundaries": [
                ("\uFFFF", b'"\xef\xbf\xbf"\n'),
                ("\U00010000", b'"\\uD800\\uDC00"\n'),
                ("\U000103FF", b'"\\uD800\\uDFFF"\n'),
                ("\U00010400", b'"\\uD801\\uDC00"\n'),
                ("\U0010FFFF", b'"\\uDBFF\\uDFFF"\n'),
                (["\uFFFF\U00010000\U0010FFFF"], b'["\xef\xbf\xbf\\uD800\\uDC00\\uDBFF\\uDFFF"]\n'),
            ],
            "literal-escapes": [
                (r"\uD83D\uDE00", b'"\\\\uD83D\\\\uDE00"\n'),
                ("literal \\uD83D\\uDE00 actual \U0001F600",
                 b'"literal \\\\uD83D\\\\uDE00 actual \\uD83D\\uDE00"\n'),
                ({r"\uFFFF": ["/", "\u00e9", "e\u0301"]},
                 b'{"\\\\uFFFF": ["/", "\xc3\xa9", "e\xcc\x81"]}\n'),
            ],
        }
        for index, (fixture, expected) in enumerate(fixtures[sys.argv[2]]):
            actual = materials.canonical_json(fixture)
            if actual != expected:
                raise AssertionError(f"fixture {index}: {actual!r} != {expected!r}")
        """;

    private const string DeclarationProbe = """
        import importlib.util
        import pathlib
        import sys

        spec = importlib.util.spec_from_file_location("materials", pathlib.Path(sys.argv[1]))
        materials = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(materials)

        # Retained Inspector material for TailBounds.instDecidable_d5; expected
        # identity is from the report, never computed with canonical_json.
        material = ("statement-v1(uparams=[],type=ep(bd,es(l0),ea(ec(ns(n0,9:Decidable),[]),eb(0))),"
                    "value=el(bd,es(l0),ea(ec(ns(ns(n0,9:Classical),13:propDecidable),[]),eb(0))))")
        declaration = {
            "statement_material": material,
            "schema": "declaration-statement-v1",
            "module_path": "D5/S0/Asymptotics/Bonferroni/TailBounds.lean",
            "kind": "def",
            "declaration_name_key": "ns(ns(ns(ns(ns(ns(n0,2:D5),2:S0),11:Asymptotics),10:Bonferroni),10:TailBounds),16:instDecidable_d5)",
        }
        expected = (
            b'{"declaration_name_key": "ns(ns(ns(ns(ns(ns(n0,2:D5),2:S0),11:Asymptotics),10:Bonferroni),10:TailBounds),16:instDecidable_d5)", '
            b'"kind": "def", "module_path": "D5/S0/Asymptotics/Bonferroni/TailBounds.lean", '
            b'"schema": "declaration-statement-v1", '
            b'"statement_material": "statement-v1(uparams=[],type=ep(bd,es(l0),ea(ec(ns(n0,9:Decidable),[]),eb(0))),'
            b'value=el(bd,es(l0),ea(ec(ns(ns(n0,9:Classical),13:propDecidable),[]),eb(0))))"}\n'
        )
        actual = materials.canonical_json(declaration)
        assert actual == expected, (actual, expected)
        assert materials.statement_address(actual) == "sha256:5e1850dbdb2d7b7705f305837c8d7bfb358abf64299075dc930d12922c844981"
        nested = {"modules": [{"declarations": [declaration]}]}
        assert materials.canonical_json(nested) == b'{"modules": [{"declarations": [' + expected[:-1] + b']}]}\n'
        """;

    private const string RejectionProbe = """
        import importlib.util
        import pathlib
        import sys

        spec = importlib.util.spec_from_file_location("materials", pathlib.Path(sys.argv[1]))
        materials = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(materials)

        def require_raises(expected_exception, value):
            try:
                materials.canonical_json(value)
            except expected_exception:
                return
            except Exception as error:
                raise AssertionError(
                    f"expected {expected_exception.__name__}, got {type(error).__name__}"
                ) from error
            raise AssertionError(f"expected {expected_exception.__name__}")

        if sys.argv[2] == "non-finite":
            for value in (float("nan"), float("inf"), float("-inf")):
                for fixture in (value, {"nested": [value]}, {value: "key"}):
                    require_raises(ValueError, fixture)
            assert materials.canonical_json(1.25) == b"1.25\n"
        elif sys.argv[2] == "lone-surrogate":
            for scalar in (0xD800, 0xDFFF):
                for fixture in (chr(scalar), {"nested": [chr(scalar)]}, {chr(scalar): "key"}):
                    require_raises(UnicodeEncodeError, fixture)
            expected = ('"normal \u4e2d \\uD83D\\uDE00"\n').encode("utf-8")
            assert materials.canonical_json("normal \u4e2d \U0001F600") == expected
        else:
            raise AssertionError(f"unknown contract: {sys.argv[2]}")
        """;

    [Fact]
    public void CanonicalJsonMatchesLegacyBytesForAsciiBmpControlsAndStructures() =>
        AssertMatchesLegacy("bmp");

    [Fact]
    public void CanonicalJsonMatchesLegacyBytesForSupplementaryPlaneScalars() =>
        AssertMatchesLegacy("supplementary");

    [Fact]
    public void CanonicalJsonMatchesLegacyBytesAtUnicodePlaneBoundaries() =>
        AssertMatchesLegacy("boundaries");

    [Fact]
    public void CanonicalJsonPreservesLiteralEscapesAlongsideActualScalars() =>
        AssertMatchesLegacy("literal-escapes");

    [Fact]
    public void CanonicalJsonPinsRealNestedDeclarationBytesAndStatementIdentity()
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run(
            "python3",
            ["-c", DeclarationProbe, Path.Combine(root, "tools/lean-inspector/materials.py")],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
        Assert.True(
            result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void CanonicalJsonRejectsNonFiniteFloatsWithoutRejectingFiniteFloats() =>
        AssertRejectsInvalidValue("non-finite");

    [Fact]
    public void CanonicalJsonRejectsLoneSurrogatesWithoutRejectingUnicodeScalars() =>
        AssertRejectsInvalidValue("lone-surrogate");

    private static void AssertMatchesLegacy(string fixtureGroup)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run(
            "python3",
            ["-c", EquivalenceProbe, Path.Combine(root, "tools/lean-inspector/materials.py"), fixtureGroup],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
        Assert.True(
            result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
    }

    private static void AssertRejectsInvalidValue(string contract)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run(
            "python3",
            ["-c", RejectionProbe, Path.Combine(root, "tools/lean-inspector/materials.py"), contract],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
        Assert.True(
            result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
    }
}
