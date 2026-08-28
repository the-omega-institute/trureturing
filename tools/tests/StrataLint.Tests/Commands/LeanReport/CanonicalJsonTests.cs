using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CanonicalJsonTests
{
    private const string EquivalenceProbe = """
        import importlib.util
        import json
        import pathlib
        import sys

        spec = importlib.util.spec_from_file_location("materials", pathlib.Path(sys.argv[1]))
        materials = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(materials)

        def legacy(value):
            text = json.dumps(value, ensure_ascii=False, sort_keys=True,
                              separators=(", ", ": "), allow_nan=False)
            encoded = []
            for character in text:
                scalar = ord(character)
                if scalar <= 0xFFFF:
                    encoded.append(character)
                    continue
                offset = scalar - 0x10000
                encoded.append(f"\\u{0xD800 + offset // 0x400:04X}"
                               f"\\u{0xDC00 + offset % 0x400:04X}")
            return ("".join(encoded) + "\n").encode("utf-8")

        fixtures = {
            "bmp": [
                "", {}, [], "ASCII", "\u4e2d\u6587 \u03b1\u03b2\u03b3 e\u0301",
                "".join(map(chr, range(0x20))), 'quote=" slash=\\ newline=\n tab=\t',
                {"z": [3, {"b": False, "a": None}], "a": {"empty": ""}},
            ],
            "supplementary": [
                "emoji \U0001F600", "CJK-B \U00020000",
                {"\U0001F680": ["mixed \u4e2d\U0001F642", "\U00020000"]},
            ],
            "boundaries": ["\uFFFF", "\U00010000", "\U0010FFFF",
                           ["\uFFFF\U00010000\U0010FFFF"]],
        }
        for index, fixture in enumerate(fixtures[sys.argv[2]]):
            actual = materials.canonical_json(fixture)
            expected = legacy(fixture)
            if actual != expected:
                raise AssertionError(f"fixture {index}: {actual!r} != {expected!r}")
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
                require_raises(ValueError, value)
            assert materials.canonical_json(1.25) == b"1.25\n"
        elif sys.argv[2] == "lone-surrogate":
            for scalar in (0xD800, 0xDFFF):
                require_raises(UnicodeEncodeError, chr(scalar))
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
