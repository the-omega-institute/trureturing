using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class UpstreamSettlementException(string code, string detail) : Exception(detail)
{
    internal string Code { get; } = code;
}

internal interface IUpstreamLeanProcessRunner
{
    ProcessOutput Run(string executable, IReadOnlyList<string> arguments, string root, TimeSpan budget);
}

internal sealed class UpstreamLeanProcessRunner : IUpstreamLeanProcessRunner
{
    public ProcessOutput Run(string executable, IReadOnlyList<string> arguments, string root, TimeSpan budget) =>
        BoundedProcessRunner.Run(executable, arguments, root, budget, 4 * 1024 * 1024);
}

internal sealed class UpstreamProbeVerifier(IUpstreamLeanProcessRunner runner, string executable, TimeSpan budget)
{
    // Infrastructure hang guard, never a mathematical verdict. Tests inject the pinned value and a runner.
    internal static readonly TimeSpan HangGuardBudget = TimeSpan.FromMinutes(5);
    private const string Name = @"[\p{L}_][\p{L}\p{N}_'′!?]*(?:\.[\p{L}_][\p{L}\p{N}_'′!?]*)*";
    private const RegexOptions Options = RegexOptions.CultureInvariant | RegexOptions.Multiline;
    private static readonly Regex Forbidden = new(@"\b(?:sorry|sorryAx|native_decide)\b|\baxiom\s", Options);
    // Maximal runs of Lean's isIdRest alphabet (Init.Meta.Defs), including !/?,
    // apostrophes, subscripts and supplementary letter-like characters. .NET \b
    // would split legal identifiers such as def!, def₁ and def𝒜 into keywords.
    private const string IdentifierCharacter =
        @"(?:[A-Za-z0-9_'!?\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u017F"
        + @"\u0391-\u039F\u03A1-\u03A2\u03A4-\u03A9\u03B1-\u03BA\u03BC-\u03FB"
        + @"\u1F00-\u1FFE\u2100-\u214F\u2080-\u2089\u2090-\u209C\u1D62-\u1D6A\u2C7C]"
        + @"|\uD835[\uDC9C-\uDD9F])";
    private const string IdentifierAtom = @"(?:«[^»]*»|" + IdentifierCharacter + @"+)";
    private static readonly Regex Tokens = new(@"#" + IdentifierCharacter + @"+|#|"
        + IdentifierAtom + @"(?:\." + IdentifierAtom + @")*", Options);
    private static readonly Regex RawStringStart = new(@"\G(?<!" + IdentifierCharacter + @")r(?<hashes>#*)""", Options);
    private static readonly Regex CharacterLiteral = new(@"\G(?<!" + IdentifierCharacter
        + @")'(?:[\uD800-\uDBFF][\uDC00-\uDFFF]|[^'\\\r\n]|\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|[^\r\n]))'", Options);

    // Derived from Lean v4.33.0 and all lake-manifest packages, including Mathlib
    // db584cd6d46c92f209a44c0f1c829460d327499d. Pinned ordinal-sorted command tokens;
    // punctuation such as % is outside the identifier token. Hash commands use the rule below.
    private static readonly string[] UnsupportedCommands =
    [
        "abbrev", "add_aesop_rules", "add_decl_doc", "alias", "assert_exists", "assert_no_sorry",
        "assert_not_exists", "assert_not_imported", "attribute", "aux_def", "axiom", "binder_predicate",
        "builtin_cbv_simproc", "builtin_cbv_simproc_decl", "builtin_cbv_simproc_pattern", "builtin_dsimproc",
        "builtin_dsimproc_decl", "builtin_facet", "builtin_grind_propagator", "builtin_initialize",
        "builtin_simproc", "builtin_simproc_decl", "builtin_simproc_pattern", "cbv_simproc", "cbv_simproc_decl",
        "cbv_simproc_pattern", "class", "coinductive", "compile_def", "compile_inductive", "configuration",
        "custom_data", "data_type", "declare_aesop_exception", "declare_aesop_rule_sets",
        "declare_bitwise_int_theorems", "declare_bitwise_uint_theorems", "declare_command_config_elab",
        "declare_command_config_elab_legacy", "declare_config_elab", "declare_config_elab_legacy",
        "declare_core_config_elab", "declare_eval_bin", "declare_eval_bin_bitwise", "declare_eval_bin_bool_pred",
        "declare_int_theorems", "declare_simp_like_tactic", "declare_sint_simprocs", "declare_syntax_cat",
        "declare_term_config_elab", "declare_uint_simprocs", "declare_uint_theorems", "def",
        "def_eval_config_item", "def_wanted", "deprecate", "deprecated_module", "deprecated_syntax",
        "derive_eval_expr_instance_using_meta_eval", "deriving", "docs_to_verso", "dsimproc", "dsimproc_decl",
        "elab", "elab_rules", "elab_stx_quot", "end", "end_local_scope", "ensure_eval_expr_instance",
        "ensure_eval_term_expr_instances", "ensure_eval_term_instance", "erase_aesop_rules", "example", "export",
        "extend_docs", "extern_lib", "facet_data", "family_def", "flex?", "gen_cnstr_fns",
        "gen_injective_theorems", "gen_lean_encoders", "gen_toml_decoders", "gen_toml_encoders",
        "grind_annotated", "grind_pattern", "grind_propagator", "guard_decl", "guard_min_heartbeats",
        "hydrate_opaque_type", "import", "include", "inductive", "infix", "infixl", "infixr", "init_grind_norm",
        "init_quot", "initialize", "initialize_simps_projections", "initialize_simps_projections?", "input_dir",
        "input_file", "insert_to_additive_translation", "instance", "instance_wanted", "irreducible_def",
        "lean_exe", "lean_lib", "lemma", "library_data", "library_facet", "library_note", "local", "lrat_proof",
        "macro", "macro_rules", "make_elab_grind_config", "make_elab_simp_config", "meta",
        "mk_iff_of_inductive_prop", "module_data", "module_facet", "mutual", "name_poly_vars", "name_power_vars",
        "namespace", "noncomputable", "nonempty_type", "nonrec", "norm_cast_add_elim", "notation", "notation3",
        "omit", "opaque", "open", "package", "package_data", "package_facet", "partial", "post_update", "postfix",
        "postprocess_traces", "prefix", "private", "proof_wanted", "protected", "public", "recall", "recall?",
        "recommended_spelling", "register_aesop_check_option", "register_builtin_option",
        "register_error_explanation", "register_grind_attr", "register_hint", "register_label_attr",
        "register_linter_set", "register_option", "register_simp_attr", "register_sym_dsimp", "register_sym_simp",
        "register_sym_simp_attr", "register_tactic_tag", "register_try?_tactic", "reprove", "require",
        "reset_grind_attrs", "run_cmd", "run_elab", "run_meta", "run_tac", "scoped", "script", "seal", "section",
        "set_library_suggestions", "set_option", "show_panel_widgets", "simproc", "simproc_decl",
        "simproc_pattern", "stop_at_first_error", "structure", "sudo", "suppress_compilation", "syntax",
        "tactic_extension", "target", "test", "test_extern", "theorem_wanted", "to_additive_name_hint",
        "to_dual_insert_cast", "to_dual_insert_cast_fun", "to_dual_name_hint", "unif_hint", "universe",
        "unlock_limits", "unsafe", "unseal", "unset_option", "unsuppress_compilation", "variable", "variable?",
        "variables", "wait_for_cancel_once_command", "whatsnew", "with_weak_namespace",
    ];

    internal static UpstreamProbeVerifier Production()
    {
        if (!LeanLakeExecutable.TryResolve(out var lake, out var reason)) throw new InvalidOperationException(reason);
        return new(new UpstreamLeanProcessRunner(), lake, HangGuardBudget);
    }

    internal ImmutableArray<string> Verify(string root, byte[] source, string manifest, ImmutableArray<string> declarations)
    {
        var text = new UTF8Encoding(false, true).GetString(source);
        var syntax = ScanProbe(text);
        var imports = syntax.Imports;
        var modules = imports.SelectMany(line => line.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries)).ToArray();
        if (modules.Length == 0 || modules.Any(module => module == "D5" || module.StartsWith("D5.", StringComparison.Ordinal)))
            throw Invalid("PROBE_IMPORTS_PROJECT", "probe must import pinned upstream modules and cannot import D5");
        using (var document = JsonDocument.Parse(manifest))
        {
            var packages = document.RootElement.GetProperty("packages").EnumerateArray()
                .Select(package => package.GetProperty("name").GetString()!).ToArray();
            foreach (var module in modules)
            {
                if (!Regex.IsMatch(module, "^" + Name + @"\z", Options)
                    || !packages.Any(package => IsPackageName(package)
                        && File.Exists(Path.Combine(root, ".lake", "packages", package, module.Replace('.', '/') + ".lean"))))
                    throw Invalid("PROBE_IMPORTS_PROJECT", $"import outside pinned manifest closure: {module}");
            }
        }
        if (Forbidden.IsMatch(text)) throw Invalid("PROBE_FAILED", "probe source contains a forbidden proof command");
        if (syntax.Theorems.Length == 0
            || syntax.Theorems.Distinct(StringComparer.Ordinal).Count() != syntax.Theorems.Length
            || !syntax.Theorems.Order(StringComparer.Ordinal).SequenceEqual(syntax.Prints.Order(StringComparer.Ordinal)))
            throw Invalid("PROBE_AXIOMS", "use named top-level theorems followed by exactly one #print axioms per theorem");
        var scratch = Path.Combine(root, ".lake");
        // Reject scratch aliases as well as input aliases: Lean must execute within this worktree.
        RequireNoLinks(root, scratch);
        Directory.CreateDirectory(scratch);
        var probePath = Path.Combine(scratch, $"upstream-probe-{Guid.NewGuid():N}.lean");
        var checkPath = Path.Combine(scratch, $"upstream-check-{Guid.NewGuid():N}.lean");
        try
        {
            File.WriteAllBytes(probePath, source);
            var compiled = runner.Run(executable, ["env", "lean", probePath], root, budget);
            var stdout = Encoding.UTF8.GetString(compiled.StandardOutput);
            var diagnostics = stdout + Encoding.UTF8.GetString(compiled.StandardError);
            if (compiled.ExitCode != 0 || Forbidden.IsMatch(diagnostics))
                throw Invalid("PROBE_FAILED", $"exit={compiled.ExitCode}\n{diagnostics}");
            var axioms = ParseAxioms(syntax.Theorems, stdout);
            var checkSource = string.Join('\n', imports.Select(line => "import " + line)) + "\n"
                + string.Concat(declarations.Select(name => "#check @" + name + "\n"));
            File.WriteAllText(checkPath, checkSource, new UTF8Encoding(false));
            var checkedNames = runner.Run(executable, ["env", "lean", checkPath], root, budget);
            var checkDiagnostics = Encoding.UTF8.GetString(checkedNames.StandardOutput)
                + Encoding.UTF8.GetString(checkedNames.StandardError);
            if (checkedNames.ExitCode != 0 || Regex.IsMatch(checkDiagnostics, @"\berror:", Options))
            {
                // Each generated #check occupies one line. Successful output and names mentioned
                // inside an unrelated error are not evidence that those declarations failed.
                var errorLines = Regex.Matches(checkDiagnostics, @":([0-9]+):[0-9]+: error:", Options)
                    .Select(match => int.Parse(match.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture) - imports.Length - 1)
                    .Where(index => index >= 0 && index < declarations.Length).Select(index => declarations[index]);
                var failures = errorLines.ToHashSet(StringComparer.Ordinal);
                var ordered = declarations.Where(failures.Contains).ToArray();
                var first = ordered.FirstOrDefault() ?? "unattributed-resolver-error";
                throw Invalid("DECLARATION_UNRESOLVED", $"{first} unresolved=[{string.Join(',', ordered)}] exit={checkedNames.ExitCode}\n{checkDiagnostics}");
            }
            return axioms;
        }
        finally
        {
            File.Delete(checkPath);
            File.Delete(probePath);
        }
    }

    private static ImmutableArray<string> ParseAxioms(string[] theorems, string stdout)
    {
        var parsed = new HashSet<string>(StringComparer.Ordinal);
        var union = new SortedSet<string>(StringComparer.Ordinal);
        foreach (Match match in Regex.Matches(stdout,
                     @"^'(?<name>[^\r\n]+)' (?:depends on axioms: \[(?<axioms>[^\]\r\n]*)\]|does not depend on any axioms)[ \t]*\r?$", Options))
        {
            if (!theorems.Contains(match.Groups["name"].Value, StringComparer.Ordinal)) continue;
            if (!parsed.Add(match.Groups["name"].Value)) throw Invalid("PROBE_AXIOMS", "duplicate axiom output");
            foreach (var axiom in match.Groups["axioms"].Value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
            {
                if (!DigestionUpstream.IsAllowedAxiom(axiom)) throw Invalid("PROBE_AXIOMS", $"unlicensed axiom: {axiom}");
                union.Add(axiom);
            }
        }
        if (theorems.Any(name => !parsed.Contains(name))) throw Invalid("PROBE_AXIOMS", "theorem lacks parsed axiom output");
        return [.. union];
    }

    private static bool IsPackageName(string name) => name.Length > 0 && name.All(c => char.IsAsciiLetterOrDigit(c) || c is '_' or '-');

    internal static void RequireNoLinks(string root, string path)
    {
        var relative = Path.GetRelativePath(root, path);
        var cursor = Path.GetFullPath(root);
        foreach (var part in relative.Split(Path.DirectorySeparatorChar))
        {
            cursor = Path.Combine(cursor, part);
            if (new FileInfo(cursor).LinkTarget is not null || new DirectoryInfo(cursor).LinkTarget is not null)
                throw Invalid("PROBE_PATH_INVALID", "probe and scratch paths cannot traverse symbolic links");
        }
    }

    private sealed record ProbeSyntax(string[] Imports, string[] Theorems, string[] Prints);

    private static ProbeSyntax ScanProbe(string source)
    {
        var lines = WithoutCommentsAndStrings(source).Split('\n');
        var original = source.Split('\n');
        var imports = new List<string>();
        var theorems = new List<string>();
        var prints = new List<string>();
        var inTheorem = false;
        var inHeader = true;
        var headerEnd = 0;
        for (var i = 0; i < lines.Length; i++)
        {
            var line = lines[i].TrimEnd('\r');
            if (string.IsNullOrWhiteSpace(line)) continue;
            var theorem = Regex.Match(line, @"\Atheorem[ \t]+(" + Name + @")(?=[ \t:({]|\z)", Options);
            if (theorem.Success) inHeader = false;
            // Validate the original import line: masking a comment must never turn a
            // continuation, trailing comment or empty module list into an accepted import.
            if (inHeader && Regex.IsMatch(line, @"\bimport\b", Options))
            {
                var import = Regex.Match(original[i].TrimEnd('\r'),
                    @"\Aimport[ \t]+(" + Name + @"(?:[ \t]+" + Name + @")*)[ \t]*\z", Options);
                if (!import.Success) throw Invalid("PROBE_IMPORT_SYNTAX", $"line={i + 1}: use a single-line import with module names only");
                if (theorems.Count > 0 || prints.Count > 0)
                    throw Invalid("PROBE_IMPORT_SYNTAX", $"line={i + 1}: imports must precede theorems");
                imports.Add(import.Groups[1].Value);
                inTheorem = false;
                headerEnd = i + 1;
                continue;
            }
            if (inHeader && Regex.IsMatch(line, @"\Aopen[ \t]+" + Name + @"(?:[ \t]+" + Name + @")*[ \t]*\z", Options))
            {
                headerEnd = i + 1;
                continue;
            }
            inHeader = false;
            if (line[0] is ' ' or '\t')
            {
                // Lean may still parse an indented declaration as a command. Indentation
                // alone cannot exempt another declaration from the theorem inventory.
                if (!inTheorem || Regex.IsMatch(line.TrimStart(),
                        @"\A(?:theorem|open|def|noncomputable|abbrev|instance|lemma|example|structure|inductive|opaque|axiom|macro|elab|syntax|notation|set_option|namespace|section|end|variable|universe|attribute|private|protected|public|meta)\b|\A[#@]", Options))
                    throw Invalid("PROBE_DECLARATION_UNSUPPORTED", $"line={i + 1}: only theorem bodies may be indented");
                continue;
            }
            var print = Regex.Match(line, @"\A#print[ \t]+axioms[ \t]+(" + Name + @")[ \t]*\z", Options);
            if (print.Success)
            {
                prints.Add(print.Groups[1].Value);
                inTheorem = false;
                continue;
            }
            if (!theorem.Success)
                throw Invalid("PROBE_DECLARATION_UNSUPPORTED", $"line={i + 1}: allowed commands are import, open, theorem and #print axioms");
            if (prints.Count > 0) throw Invalid("PROBE_AXIOMS", "#print axioms commands must form the trailing block");
            inTheorem = theorem.Success;
            if (theorem.Success) theorems.Add(theorem.Groups[1].Value);
        }
        if (CheckCommandTokens(string.Join('\n', lines.Skip(headerEnd))) != theorems.Count)
            throw Invalid("PROBE_DECLARATION_UNSUPPORTED", "every theorem token must start an inventoried theorem");
        return new([.. imports], [.. theorems], [.. prints]);
    }

    private static int CheckCommandTokens(string source)
    {
        var theorems = 0;
        foreach (Match token in Tokens.Matches(source))
        {
            // Hash commands are extensible: the only allowed member is the complete
            // column-zero axiom print line already inventoried by ScanProbe.
            if (token.Value.StartsWith('#'))
            {
                if (token.Value != "#print" || (token.Index > 0 && source[token.Index - 1] != '\n')
                    || !Regex.IsMatch(source[token.Index..], @"\A#print[ \t]+axioms[ \t]+" + Name + @"[ \t]*\r?(?:\n|\z)", Options))
                    throw Invalid("PROBE_DECLARATION_UNSUPPORTED", $"command token outside probe dialect: {token.Value}");
                continue;
            }
            // Dotted names are single identifiers, but a leading unescaped command
            // keyword still starts a command (def.x); only later segments are exempt.
            if (token.Value.StartsWith('«')) continue;
            var dot = token.Value.IndexOf('.');
            var first = dot < 0 ? token.Value : token.Value[..dot];
            if (Array.BinarySearch(UnsupportedCommands, first, StringComparer.Ordinal) >= 0)
                throw Invalid("PROBE_DECLARATION_UNSUPPORTED", $"command token outside probe dialect: {token.Value}");
            if (first == "theorem")
            {
                if (token.Index > 0 && source[token.Index - 1] != '\n')
                    throw Invalid("PROBE_DECLARATION_UNSUPPORTED", $"{token.Value} must start at column 0");
                theorems++;
            }
        }
        return theorems;
    }

    private static string WithoutCommentsAndStrings(string source)
    {
        var chars = source.ToCharArray();
        var depth = 0;
        var line = false;
        var quoted = false;
        var escaped = false;
        var rawHashes = -1;
        for (var i = 0; i < chars.Length; i++)
        {
            var c = source[i];
            if (rawHashes >= 0)
            {
                if (c is not '\n' and not '\r') chars[i] = ' ';
                if (c == '"')
                {
                    var end = i + 1;
                    // Consume exactly the delimiter's k hashes; any extra # is code.
                    while (end < source.Length && end - i - 1 < rawHashes && source[end] == '#') end++;
                    if (end - i - 1 == rawHashes)
                    {
                        Array.Fill(chars, ' ', i, end - i);
                        i = end - 1;
                        rawHashes = -1;
                    }
                }
                continue;
            }
            if (quoted)
            {
                if (!escaped && c == '"') quoted = false;
                escaped = !escaped && c == '\\';
                if (c is not '\n' and not '\r') chars[i] = ' ';
                continue;
            }
            if (depth == 0 && !line && c == 'r')
            {
                var raw = RawStringStart.Match(source, i);
                if (raw.Success)
                {
                    rawHashes = raw.Groups["hashes"].Length;
                    Array.Fill(chars, ' ', i, raw.Length);
                    i += raw.Length - 1;
                    continue;
                }
            }
            if (depth == 0 && !line && c == '\'')
            {
                var literal = CharacterLiteral.Match(source, i);
                if (literal.Success)
                {
                    Array.Fill(chars, ' ', i, literal.Length);
                    i += literal.Length - 1;
                    continue;
                }
            }
            if (depth == 0 && !line && c == '"')
            { quoted = true; chars[i] = ' '; continue; }
            if (depth == 0 && !line && i + 1 < chars.Length && c == '-' && source[i + 1] == '-') line = true;
            if (!line && i + 1 < chars.Length && c == '/' && source[i + 1] == '-')
            { depth++; chars[i++] = ' '; chars[i] = ' '; continue; }
            if (!line && depth > 0 && i + 1 < chars.Length && c == '-' && source[i + 1] == '/')
            { depth--; chars[i++] = ' '; chars[i] = ' '; continue; }
            if (c == '\n') line = false;
            else if (c != '\r' && (line || depth > 0)) chars[i] = ' ';
        }
        if (quoted || rawHashes >= 0 || depth > 0) throw Invalid("PROBE_DECLARATION_UNSUPPORTED", "unterminated string or block comment");
        return new string(chars);
    }

    private static UpstreamSettlementException Invalid(string code, string detail) => new(code, detail);
}
