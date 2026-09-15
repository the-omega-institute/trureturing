using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class UpstreamProbeVerifierTests
{
    [Fact]
    public void SameLineTrailingCommandIsRejected() => AssertDialectRejected(
        "theorem probe : True := True.intro def hidden := 1\n#print axioms probe\n");

    [Fact]
    public void SameLineSecondTheoremIsRejected() => AssertDialectRejected(
        "theorem probe : True := True.intro theorem hidden (p : Prop) : p ∨ ¬p := Classical.em p\n#print axioms probe\n");

    [Fact]
    public void IndentedInitializeIsRejected() => AssertDialectRejected(
        "theorem probe : True := True.intro\n  initialize hidden : Nat ← pure 1\n#print axioms probe\n");

    [Fact]
    public void IndentedNonrecDefIsRejected() => AssertDialectRejected(
        "theorem probe : True := True.intro\n  nonrec def hidden := 1\n#print axioms probe\n");

    // Pinned command vocabulary: no host toolchain or package reads in this fixture.
    public static IEnumerable<object[]> UnsupportedCommandKeywords()
    {
        const string keywords =
            "abbrev add_aesop_rules add_decl_doc alias assert_exists " +
            "assert_no_sorry assert_not_exists assert_not_imported attribute aux_def " +
            "axiom binder_predicate builtin_cbv_simproc builtin_cbv_simproc_decl builtin_cbv_simproc_pattern " +
            "builtin_dsimproc builtin_dsimproc_decl builtin_facet builtin_grind_propagator builtin_initialize " +
            "builtin_simproc builtin_simproc_decl builtin_simproc_pattern cbv_simproc cbv_simproc_decl " +
            "cbv_simproc_pattern class coinductive compile_def compile_inductive " +
            "configuration custom_data data_type declare_aesop_exception declare_aesop_rule_sets " +
            "declare_bitwise_int_theorems declare_bitwise_uint_theorems declare_command_config_elab declare_command_config_elab_legacy declare_config_elab " +
            "declare_config_elab_legacy declare_core_config_elab declare_eval_bin declare_eval_bin_bitwise declare_eval_bin_bool_pred " +
            "declare_int_theorems declare_simp_like_tactic declare_sint_simprocs declare_syntax_cat declare_term_config_elab " +
            "declare_uint_simprocs declare_uint_theorems def def_eval_config_item deprecate " +
            "deprecated_module deprecated_syntax derive_eval_expr_instance_using_meta_eval deriving docs_to_verso " +
            "dsimproc dsimproc_decl elab elab_rules elab_stx_quot " +
            "end end_local_scope ensure_eval_expr_instance ensure_eval_term_expr_instances ensure_eval_term_instance " +
            "erase_aesop_rules example export extend_docs extern_lib " +
            "facet_data family_def flex? gen_cnstr_fns gen_injective_theorems " +
            "gen_lean_encoders gen_toml_decoders gen_toml_encoders grind_annotated grind_pattern " +
            "grind_propagator guard_decl guard_min_heartbeats hydrate_opaque_type import " +
            "include inductive infix infixl infixr " +
            "init_grind_norm init_quot initialize initialize_simps_projections initialize_simps_projections? " +
            "input_dir input_file insert_to_additive_translation instance irreducible_def " +
            "lean_exe lean_lib lemma library_data library_facet " +
            "library_note local lrat_proof macro macro_rules " +
            "make_elab_grind_config make_elab_simp_config meta mk_iff_of_inductive_prop module_data " +
            "module_facet mutual name_poly_vars name_power_vars namespace " +
            "noncomputable nonempty_type nonrec norm_cast_add_elim notation " +
            "notation3 omit opaque open package " +
            "package_data package_facet partial post_update postfix " +
            "postprocess_traces prefix private protected public " +
            "recall recall? recommended_spelling register_aesop_check_option register_builtin_option " +
            "register_error_explanation register_grind_attr register_hint register_label_attr register_linter_set " +
            "register_option register_simp_attr register_sym_dsimp register_sym_simp register_sym_simp_attr " +
            "register_tactic_tag register_try?_tactic reprove require reset_grind_attrs " +
            "run_cmd run_elab run_meta run_tac scoped " +
            "script seal section set_library_suggestions set_option " +
            "show_panel_widgets simproc simproc_decl simproc_pattern stop_at_first_error " +
            "structure sudo suppress_compilation syntax tactic_extension " +
            "target test test_extern to_additive_name_hint to_dual_insert_cast " +
            "to_dual_insert_cast_fun to_dual_name_hint unif_hint universe unlock_limits " +
            "unsafe unseal unset_option unsuppress_compilation variable " +
            "variable? variables wait_for_cancel_once_command whatsnew with_weak_namespace";
        foreach (var keyword in keywords.Split(' '))
            yield return [keyword];
    }

    [Theory]
    [MemberData(nameof(UnsupportedCommandKeywords))]
    public void CommandKeywordIsRejectedAtEveryPositionAfterHeader(string keyword)
    {
        foreach (var separator in new[] { " ", "\n  ", "\n", "\n  exact " })
            AssertDialectRejected("theorem probe : True := True.intro" + separator
                + keyword + " hidden\ntheorem second : True := True.intro\n"
                + "#print axioms probe\n#print axioms second\n");
    }

    public static IEnumerable<object[]> UnsupportedHashCommands()
    {
        foreach (var command in new[]
                 {
                     "#eval! (0 : Nat)", "#synth Nat", "#guard_msgs", "#adaptation_note",
                     "#help", "#where", "#print True", " #print axioms probe",
                     "#future_package_command", "#"
                 })
        foreach (var separator in new[] { " ", "\n  ", "\n", "\n  exact " })
            yield return [command, separator];
    }

    [Theory]
    [MemberData(nameof(UnsupportedHashCommands))]
    public void HashCommandIsRejectedAtEveryPositionAfterHeader(string command, string separator) =>
        AssertDialectRejected("theorem probe : True := True.intro" + separator + command
            + "\ntheorem second : True := True.intro\n#print axioms probe\n#print axioms second\n");

    [Theory]
    [InlineData("theorem probe : True := True.intro #print axioms probe\n#print axioms probe\n")]
    [InlineData("theorem probe : True := True.intro\n  exact (#print axioms probe)\n#print axioms probe\n")]
    [InlineData("theorem probe : True := True.intro\n  exact (theorem hidden : True := True.intro)\n#print axioms probe\n")]
    public void TheoremAndPrintTokensMustStartAtColumnZero(string body) => AssertDialectRejected(body);

    [Fact]
    public void TacticWordsContainingKeywordPrefixesAreAccepted()
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\nopen Nat\ntheorem probe : True → True := by\n"
            + "  intro definitely\n  let defer : Nat := default\n  exact definitely\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(source, f.Runner.Sources[0]);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Theory]
    [InlineData("def'")]
    [InlineData("def!")]
    [InlineData("def?")]
    [InlineData("def₁")]
    [InlineData("defα")]
    [InlineData("αdef")]
    [InlineData("def𝒜")]
    [InlineData("𝒜def")]
    [InlineData("_def")]
    [InlineData("def1")]
    [InlineData("theorem'")]
    [InlineData("imported")]
    [InlineData("definitional_lemma_ex")]
    [InlineData("example_h")]
    [InlineData("default")]
    public void LeanIdentifierContinuationsDoNotCreateCommandTokens(string name)
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : True := by\n  let " + name
            + " : Nat := 1\n  trivial\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    [Fact]
    public void MaskedCommandTokensDoNotAffectTheoremOrPrintCounts()
    {
        using var f = new ProbeFixture();
        var source = "import Mathlib\ntheorem probe : True := by\n"
            + "  /- initialize /- theorem -/ #print axioms -/\n"
            + "  let note := \"nonrec def theorem #print axioms\"\n"
            + "  trivial -- theorem initialize #print axioms\n#print axioms probe\n";
        Assert.Equal(3, f.Verify(source).Length);
        Assert.Equal(2, f.Runner.Sources.Count);
    }

    private static void AssertDialectRejected(string body)
    {
        using var f = new ProbeFixture();
        f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes("'probe' does not depend on any axioms\n"), []));
        var error = Assert.Throws<UpstreamSettlementException>(() => f.Verify("import Mathlib\n" + body));
        Assert.Equal("PROBE_DECLARATION_UNSUPPORTED", error.Code);
        Assert.Empty(f.Runner.Sources);
    }
}
