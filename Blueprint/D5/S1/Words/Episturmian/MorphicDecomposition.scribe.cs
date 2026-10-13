using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Episturmian;

internal sealed class MorphicDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Episturmian/MorphicDecomposition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Rewriting/justinpirillo2002episturmian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Episturmian words: MorphicDecomposition.", H("MorphicDecomposition"),
        Blocks(
            Node("central-prefix-succ-0", "central prefix succ", DeclarationHandle.Create(Prefix + "central_prefix_succ"), Disp(Formula0()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("central-prefix-of-le-1", "central prefix of le", DeclarationHandle.Create(Prefix + "central_prefix_of_le"), Disp(Formula1()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("central-get-eq-cdelta-2", "central get eq cDelta", DeclarationHandle.Create(Prefix + "central_get_eq_cDelta"), Disp(Formula2()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("central-is-cdelta-prefix-3", "central is cDelta prefix", DeclarationHandle.Create(Prefix + "central_is_cDelta_prefix"), Disp(Formula3()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("letterimage-4", "letterImage", DeclarationHandle.Create(Prefix + "letterImage"), Disp(Formula4()), "The displayed equations define the object.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("mu-5", "mu", DeclarationHandle.Create(Prefix + "mu"), Disp(Formula5()), "The displayed equations define the object.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("mu-length-step-6", "mu length step", DeclarationHandle.Create(Prefix + "mu_length_step"), Disp(Formula6()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("mu-length-pos-7", "mu length pos", DeclarationHandle.Create(Prefix + "mu_length_pos"), Disp(Formula7()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("mu-length-triangle-8", "mu length triangle", DeclarationHandle.Create(Prefix + "mu_length_triangle"), Disp(Formula8()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("mu-length-at-run-start-9", "mu length at run start", DeclarationHandle.Create(Prefix + "mu_length_at_run_start"), Disp(Formula9()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("mu-constant-run-13", "mu constant run", DeclarationHandle.Create(Prefix + "mu_constant_run"), Disp(Formula13()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("lword-14", "Lword", DeclarationHandle.Create(Prefix + "Lword"), Disp(Formula14()), "The displayed equations define the object.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("hword-15", "Hword", DeclarationHandle.Create(Prefix + "Hword"), Disp(Formula15()), "The displayed equations define the object.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("letterimage-conjugacy-16", "letterImage conjugacy", DeclarationHandle.Create(Prefix + "letterImage_conjugacy"), Disp(Formula16()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-reverse-17", "Hword reverse", DeclarationHandle.Create(Prefix + "Hword_reverse"), Disp(Formula17()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-starts-18", "Hword starts", DeclarationHandle.Create(Prefix + "Hword_starts"), Disp(Formula18()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-cons-19", "Hword cons", DeclarationHandle.Create(Prefix + "Hword_cons"), Disp(Formula19()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-injective-20", "Hword injective", DeclarationHandle.Create(Prefix + "Hword_injective"), Disp(Formula20()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-palindrome-iff-21", "Hword palindrome iff", DeclarationHandle.Create(Prefix + "Hword_palindrome_iff"), Disp(Formula21()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("lword-append-22", "Lword append", DeclarationHandle.Create(Prefix + "Lword_append"), Disp(Formula22()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("lword-prefix-23", "Lword prefix", DeclarationHandle.Create(Prefix + "Lword_prefix"), Disp(Formula23()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-suffix-decode-24", "Hword suffix decode", DeclarationHandle.Create(Prefix + "Hword_suffix_decode"), Disp(Formula24()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palindrome-suffix-hword-starts-25", "palindrome suffix Hword starts", DeclarationHandle.Create(Prefix + "palindrome_suffix_Hword_starts"), Disp(Formula25()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-palcut-26", "Hword palCut", DeclarationHandle.Create(Prefix + "Hword_palCut"), Disp(Formula26()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-palclosure-27", "Hword palClosure", DeclarationHandle.Create(Prefix + "Hword_palClosure"), Disp(Formula27()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("lword-suffix-nonx-28", "Lword suffix nonx", DeclarationHandle.Create(Prefix + "Lword_suffix_nonx"), Disp(Formula28()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palindrome-suffix-last-starts-29", "palindrome suffix last starts", DeclarationHandle.Create(Prefix + "palindrome_suffix_last_starts"), Disp(Formula29()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palcut-le-of-suffix-30", "palCut le of suffix", DeclarationHandle.Create(Prefix + "palCut_le_of_suffix"), Disp(Formula30()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("lword-palclosure-31", "Lword palClosure", DeclarationHandle.Create(Prefix + "Lword_palClosure"), Disp(Formula31()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palclosure-of-palindrome-32", "palClosure of palindrome", DeclarationHandle.Create(Prefix + "palClosure_of_palindrome"), Disp(Formula32()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("hword-append-letter-closure-33", "Hword append letter closure", DeclarationHandle.Create(Prefix + "Hword_append_letter_closure"), Disp(Formula33()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("central-justin-35", "central Justin", DeclarationHandle.Create(Prefix + "central_Justin"), Disp(Formula35()), "Justin–Pirillo, equation (3): the palindromic-prefix morphism identity. Here cons is Mathlib Stream'.cons, which prepends one letter to a directive stream.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("central-justin-shift-36", "central Justin shift", DeclarationHandle.Create(Prefix + "central_Justin_shift"), Disp(Formula36()), "Justin–Pirillo, equation (3): the palindromic-prefix morphism identity.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("muword-37", "muWord", DeclarationHandle.Create(Prefix + "muWord"), Disp(Formula37()), "The displayed equations define the object.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("mu-shift-38", "mu shift", DeclarationHandle.Create(Prefix + "mu_shift"), Disp(Formula38()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("central-morphic-finite-39", "central morphic finite", DeclarationHandle.Create(Prefix + "central_morphic_finite"), Disp(Formula39()), "Justin–Pirillo, equation (3): the palindromic-prefix morphism identity.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("morphicimage-40", "MorphicImage", DeclarationHandle.Create(Prefix + "MorphicImage"), Disp(Formula40()), "The displayed equations define the object.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("wordprefix-isprefix-41", "wordPrefix isPrefix", DeclarationHandle.Create(Prefix + "wordPrefix_isPrefix"), Disp(Formula41()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("cdelta-morphicimage-42", "cDelta morphicImage", DeclarationHandle.Create(Prefix + "cDelta_morphicImage"), Disp(Formula42()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, DeclarationHandle declaration, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(id), declaration, H(title), StatementSource.FromAuthor(formula), provenance,
        Narrative(title, prose), role);


    private static BlockSequence Narrative(string title, string prose) => title is "claim" or "result"
        ? Blocks(
            Paragraph(DefinitionDsl.Text("Let "), Math(Seq(Mathbf, Grp(F.Id("t")))),
                DefinitionDsl.Text(" be an aperiodic episturmian word. Then "),
                Math(Rel(App(F.Id("dio"), Seq(Mathbf, Grp(F.Id("t")))), FormulaRelationOperator.LessThan, Infty)),
                DefinitionDsl.Text(" if and only if "), Math(Seq(Mathbf, Grp(F.Id("t")))),
                DefinitionDsl.Text(" has bounded partial quotients.")),
            Paragraph(DefinitionDsl.Text("Peltomäki, Conjecture 8.4, Section 8.")),
            Paragraph(DefinitionDsl.Text(prose)))
        : Blocks(Paragraph(DefinitionDsl.Text(prose)));

    private static Formula PrefixExpression() => Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id("z"), Colon, Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))))), Comma, Sp, LambdaLower, Sp, Parenthesized(Seq(F.Id("n"), Colon, F.Id("Nat"))), Comma, Sp, App(F.Id("factor"), F.Id("z"), D(0), F.Id("n"))));

    private static Formula WordPowerExpression() => Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id("W"), Colon, App(F.Id("List"), App(F.Id("Fin"), F.Id("d"))))), Comma, Sp, LambdaLower, Sp, Parenthesized(Seq(F.Id("a"), Colon, F.Id("Nat"))), Comma, Sp, App(F.Id("wordPower"), F.Id("a"), F.Id("W"))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Arrow(Formula left, Formula right) => Parenthesized(new Formula.TypeArrow(Parenthesized(left), Parenthesized(right)));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Parenthesized(type), body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Parenthesized(type), body);

    private static Formula Formula0() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("k", F.Id("Nat"), App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), App(App(F.Id("central"), F.Id("Delta")), F.Id("k")), App(App(F.Id("central"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("k")), Plus, Parenthesized(D(1)))))))));

    private static Formula Formula1() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("k", F.Id("Nat"), All("m", F.Id("Nat"), Imp(Rel(F.Id("k"), FormulaRelationOperator.LessThanOrEqual, F.Id("m")), App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), App(App(F.Id("central"), F.Id("Delta")), F.Id("k")), App(App(F.Id("central"), F.Id("Delta")), F.Id("m"))))))));

    private static Formula Formula2() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("k", F.Id("Nat"), All("i", F.Id("Nat"), Imp(Rel(F.Id("i"), FormulaRelationOperator.LessThan, Seq(Parenthesized(Parenthesized(App(App(F.Id("central"), F.Id("Delta")), F.Id("k")))), Dot, F.Id("length"))), Rel(Seq(Parenthesized(Parenthesized(App(App(F.Id("central"), F.Id("Delta")), F.Id("k")))), OpenBracket, F.Id("i"), CloseBracket), FormulaRelationOperator.Equal, App(App(F.Id("cDelta"), F.Id("Delta")), F.Id("i"))))))));

    private static Formula Formula3() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("k", F.Id("Nat"), Rel(App(App(PrefixExpression(), Parenthesized(App(F.Id("cDelta"), F.Id("Delta")))), Seq(Parenthesized(Parenthesized(App(App(F.Id("central"), F.Id("Delta")), F.Id("k")))), Dot, F.Id("length"))), FormulaRelationOperator.Equal, App(App(F.Id("central"), F.Id("Delta")), F.Id("k"))))));

    private static Formula Formula4() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("z", App(F.Id("Fin"), F.Id("d")), Rel(App(App(F.Id("letterImage"), F.Id("x")), F.Id("z")), FormulaRelationOperator.Equal, Parenthesized(Seq(F.Id("if"), Sp, Parenthesized(Rel(F.Id("z"), FormulaRelationOperator.Equal, F.Id("x"))), Sp, F.Id("then"), Sp, Parenthesized(Seq(OpenBracket, F.Id("x"), CloseBracket)), Sp, F.Id("else"), Sp, Parenthesized(Seq(OpenBracket, F.Id("x"), Comma, F.Id("z"), CloseBracket))))))));

    private static Formula Formula5() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), And(All("z", App(F.Id("Fin"), F.Id("d")), Rel(App(App(App(F.Id("mu"), F.Id("Delta")), Parenthesized(D(0))), Parenthesized(F.Id("z"))), FormulaRelationOperator.Equal, Seq(OpenBracket, F.Id("z"), CloseBracket))), All("z", App(F.Id("Fin"), F.Id("d")), All("n", F.Id("Nat"), Rel(App(App(App(F.Id("mu"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(D(1))))), Parenthesized(F.Id("z"))), FormulaRelationOperator.Equal, App(Seq(Parenthesized(Parenthesized(App(App(F.Id("letterImage"), Parenthesized(App(F.Id("Delta"), F.Id("n")))), F.Id("z")))), Dot, F.Id("flatMap")), Parenthesized(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n"))))))))));

    private static Formula Formula6() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), All("z", App(F.Id("Fin"), F.Id("d")), Rel(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(D(1))))), F.Id("z")))), Dot, F.Id("length")), FormulaRelationOperator.Equal, Seq(F.Id("if"), Sp, Parenthesized(Rel(F.Id("z"), FormulaRelationOperator.Equal, App(F.Id("Delta"), F.Id("n")))), Sp, F.Id("then"), Sp, Parenthesized(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("z")))), Dot, F.Id("length"))), Sp, F.Id("else"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), Parenthesized(App(F.Id("Delta"), F.Id("n")))))), Dot, F.Id("length"))), Plus, Parenthesized(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("z")))), Dot, F.Id("length")))))))))));

    private static Formula Formula7() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), All("z", App(F.Id("Fin"), F.Id("d")), Rel(D(0), FormulaRelationOperator.LessThan, Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("z")))), Dot, F.Id("length")))))));

    private static Formula Formula8() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), All("u", App(F.Id("Fin"), F.Id("d")), All("v", App(F.Id("Fin"), F.Id("d")), All("z", App(F.Id("Fin"), F.Id("d")), Imp(Rel(F.Id("u"), FormulaRelationOperator.NotEqual, F.Id("v")), Rel(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("z")))), Dot, F.Id("length")), FormulaRelationOperator.LessThanOrEqual, Seq(Parenthesized(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("u")))), Dot, F.Id("length"))), Plus, Parenthesized(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("v")))), Dot, F.Id("length"))))))))))));

    private static Formula Formula9() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), Imp(Or(Rel(F.Id("n"), FormulaRelationOperator.Equal, D(0)), Rel(App(F.Id("Delta"), Parenthesized(Seq(Parenthesized(F.Id("n")), Minus, Parenthesized(D(1))))), FormulaRelationOperator.NotEqual, App(F.Id("Delta"), F.Id("n")))), All("z", App(F.Id("Fin"), F.Id("d")), Rel(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("z")))), Dot, F.Id("length")), FormulaRelationOperator.LessThanOrEqual, Seq(Parenthesized(D(2)), Cdot, Sp, Parenthesized(Seq(Parenthesized(Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), Parenthesized(App(F.Id("Delta"), F.Id("n")))))), Dot, F.Id("length"))))))))));




    private static Formula Formula13() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), All("a", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("z", App(F.Id("Fin"), F.Id("d")), Imp(All("i", F.Id("Nat"), Imp(Rel(F.Id("i"), FormulaRelationOperator.LessThan, F.Id("a")), Rel(App(F.Id("Delta"), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(F.Id("i"))))), FormulaRelationOperator.Equal, F.Id("x")))), Rel(App(App(App(F.Id("mu"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(F.Id("a"))))), F.Id("z")), FormulaRelationOperator.Equal, Seq(F.Id("if"), Sp, Parenthesized(Rel(F.Id("z"), FormulaRelationOperator.Equal, F.Id("x"))), Sp, F.Id("then"), Sp, Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("x"))), Sp, F.Id("else"), Sp, Parenthesized(Seq(Parenthesized(App(App(WordPowerExpression(), Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("x")))), F.Id("a"))), Plus, Plus, Parenthesized(App(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")), F.Id("z"))))))))))))));

    private static Formula Formula14() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(App(F.Id("Lword"), F.Id("x")), F.Id("w")), FormulaRelationOperator.Equal, Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("flatMap")), Parenthesized(App(F.Id("letterImage"), F.Id("x")))))))));

    private static Formula Formula15() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(App(F.Id("Hword"), F.Id("x")), F.Id("w")), FormulaRelationOperator.Equal, Parenthesized(Seq(Parenthesized(App(App(F.Id("Lword"), F.Id("x")), F.Id("w"))), Plus, Plus, Parenthesized(Seq(OpenBracket, F.Id("x"), CloseBracket))))))));

    private static Formula Formula16() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("z", App(F.Id("Fin"), F.Id("d")), Rel(Seq(Parenthesized(Seq(OpenBracket, F.Id("x"), CloseBracket)), Plus, Plus, Parenthesized(Seq(Parenthesized(Parenthesized(App(App(F.Id("letterImage"), F.Id("x")), F.Id("z")))), Dot, F.Id("reverse")))), FormulaRelationOperator.Equal, Seq(Parenthesized(App(App(F.Id("letterImage"), F.Id("x")), F.Id("z"))), Plus, Plus, Parenthesized(Seq(OpenBracket, F.Id("x"), CloseBracket)))))));

    private static Formula Formula17() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(Seq(Parenthesized(Parenthesized(App(App(F.Id("Hword"), F.Id("x")), F.Id("w")))), Dot, F.Id("reverse")), FormulaRelationOperator.Equal, App(App(F.Id("Hword"), F.Id("x")), Seq(F.Id("w"), Dot, F.Id("reverse")))))));

    private static Formula Formula18() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Ex("r", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(App(F.Id("Hword"), F.Id("x")), F.Id("w")), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("x")), Colon, Colon, Parenthesized(F.Id("r"))))))));

    private static Formula Formula19() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("z", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(App(F.Id("Hword"), F.Id("x")), Parenthesized(Seq(Parenthesized(F.Id("z")), Colon, Colon, Parenthesized(F.Id("w"))))), FormulaRelationOperator.Equal, Seq(F.Id("if"), Sp, Parenthesized(Rel(F.Id("z"), FormulaRelationOperator.Equal, F.Id("x"))), Sp, F.Id("then"), Sp, Parenthesized(Seq(Parenthesized(F.Id("x")), Colon, Colon, Parenthesized(App(App(F.Id("Hword"), F.Id("x")), F.Id("w"))))), Sp, F.Id("else"), Sp, Parenthesized(Seq(Parenthesized(F.Id("x")), Colon, Colon, Parenthesized(Seq(Parenthesized(F.Id("z")), Colon, Colon, Parenthesized(App(App(F.Id("Hword"), F.Id("x")), F.Id("w")))))))))))));

    private static Formula Formula20() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), App(Seq(F.Id("Function"), Dot, F.Id("Injective")), Parenthesized(App(F.Id("Hword"), F.Id("x"))))));

    private static Formula Formula21() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Iff(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), Parenthesized(App(App(F.Id("Hword"), F.Id("x")), F.Id("w")))), App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("w"))))));

    private static Formula Formula22() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("u", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("v", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(App(F.Id("Lword"), F.Id("x")), Parenthesized(Seq(Parenthesized(F.Id("u")), Plus, Plus, Parenthesized(F.Id("v"))))), FormulaRelationOperator.Equal, Seq(Parenthesized(App(App(F.Id("Lword"), F.Id("x")), F.Id("u"))), Plus, Plus, Parenthesized(App(App(F.Id("Lword"), F.Id("x")), F.Id("v")))))))));

    private static Formula Formula23() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("u", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), F.Id("u"), F.Id("w")), App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), App(App(F.Id("Lword"), F.Id("x")), F.Id("u")), App(App(F.Id("Lword"), F.Id("x")), F.Id("w"))))))));

    private static Formula Formula24() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("s", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("IsSuffix")), F.Id("s"), App(App(F.Id("Hword"), F.Id("x")), F.Id("w"))), Imp(Ex("r", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(F.Id("s"), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("x")), Colon, Colon, Parenthesized(F.Id("r"))))), Ex("v", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), And(App(Seq(F.Id("List"), Dot, F.Id("IsSuffix")), F.Id("v"), F.Id("w")), Rel(F.Id("s"), FormulaRelationOperator.Equal, App(App(F.Id("Hword"), F.Id("x")), F.Id("v")))))))))));

    private static Formula Formula25() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("s", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("IsSuffix")), F.Id("s"), App(App(F.Id("Hword"), F.Id("x")), F.Id("w"))), Imp(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("s")), Imp(Rel(F.Id("s"), FormulaRelationOperator.NotEqual, Seq(OpenBracket, CloseBracket)), Ex("r", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(F.Id("s"), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("x")), Colon, Colon, Parenthesized(F.Id("r"))))))))))));

    private static Formula Formula26() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(F.Id("palCut"), Parenthesized(App(App(F.Id("Hword"), F.Id("x")), F.Id("w")))), FormulaRelationOperator.Equal, Seq(Parenthesized(Parenthesized(App(App(F.Id("Lword"), F.Id("x")), Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("take")), Parenthesized(App(F.Id("palCut"), F.Id("w")))))))), Dot, F.Id("length"))))));

    private static Formula Formula27() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(F.Id("palClosure"), Parenthesized(App(App(F.Id("Hword"), F.Id("x")), F.Id("w")))), FormulaRelationOperator.Equal, App(App(F.Id("Hword"), F.Id("x")), Parenthesized(App(F.Id("palClosure"), F.Id("w"))))))));

    private static Formula Formula28() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("z", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("s", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(Rel(F.Id("z"), FormulaRelationOperator.NotEqual, F.Id("x")), Imp(App(Seq(F.Id("List"), Dot, F.Id("IsSuffix")), F.Id("s"), App(App(F.Id("Lword"), F.Id("x")), F.Id("w"))), Imp(Ex("r", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(F.Id("s"), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("z")), Colon, Colon, Parenthesized(F.Id("r"))))), App(Seq(F.Id("List"), Dot, F.Id("IsSuffix")), Seq(Parenthesized(Seq(OpenBracket, F.Id("x"), CloseBracket)), Plus, Plus, Parenthesized(Seq(Parenthesized(F.Id("s")), Plus, Plus, Parenthesized(Seq(OpenBracket, F.Id("x"), CloseBracket))))), App(App(F.Id("Hword"), F.Id("x")), F.Id("w")))))))))));

    private static Formula Formula29() =>
        All("d", F.Id("Nat"), All("z", App(F.Id("Fin"), F.Id("d")), All("p", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("s", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("IsSuffix")), F.Id("s"), Seq(Parenthesized(F.Id("p")), Plus, Plus, Parenthesized(Seq(OpenBracket, F.Id("z"), CloseBracket)))), Imp(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("s")), Imp(Rel(F.Id("s"), FormulaRelationOperator.NotEqual, Seq(OpenBracket, CloseBracket)), Ex("r", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(F.Id("s"), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("z")), Colon, Colon, Parenthesized(F.Id("r"))))))))))));

    private static Formula Formula30() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("s", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("IsSuffix")), F.Id("s"), F.Id("w")), Imp(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("s")), Rel(App(F.Id("palCut"), F.Id("w")), FormulaRelationOperator.LessThanOrEqual, Seq(Parenthesized(Seq(F.Id("w"), Dot, F.Id("length"))), Minus, Parenthesized(Seq(F.Id("s"), Dot, F.Id("length"))))))))));

    private static Formula Formula31() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("z", App(F.Id("Fin"), F.Id("d")), All("p", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(Rel(F.Id("z"), FormulaRelationOperator.NotEqual, F.Id("x")), Rel(App(F.Id("palClosure"), Parenthesized(App(App(F.Id("Lword"), F.Id("x")), Parenthesized(Seq(Parenthesized(F.Id("p")), Plus, Plus, Parenthesized(Seq(OpenBracket, F.Id("z"), CloseBracket))))))), FormulaRelationOperator.Equal, App(App(F.Id("Hword"), F.Id("x")), Parenthesized(App(F.Id("palClosure"), Parenthesized(Seq(Parenthesized(F.Id("p")), Plus, Plus, Parenthesized(Seq(OpenBracket, F.Id("z"), CloseBracket)))))))))))));

    private static Formula Formula32() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("w")), Rel(App(F.Id("palClosure"), F.Id("w")), FormulaRelationOperator.Equal, F.Id("w")))));

    private static Formula Formula33() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("z", App(F.Id("Fin"), F.Id("d")), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(F.Id("palClosure"), Parenthesized(Seq(Parenthesized(App(App(F.Id("Hword"), F.Id("x")), F.Id("w"))), Plus, Plus, Parenthesized(Seq(OpenBracket, F.Id("z"), CloseBracket))))), FormulaRelationOperator.Equal, App(App(F.Id("Hword"), F.Id("x")), Parenthesized(App(F.Id("palClosure"), Parenthesized(Seq(Parenthesized(F.Id("w")), Plus, Plus, Parenthesized(Seq(OpenBracket, F.Id("z"), CloseBracket))))))))))));


    private static Formula Formula35() =>
        All("d", F.Id("Nat"), All("x", App(F.Id("Fin"), F.Id("d")), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("k", F.Id("Nat"), Rel(App(App(F.Id("central"), Parenthesized(App(App(F.Id("cons"), F.Id("x")), F.Id("Delta")))), Parenthesized(Seq(Parenthesized(F.Id("k")), Plus, Parenthesized(D(1))))), FormulaRelationOperator.Equal, App(App(F.Id("Hword"), F.Id("x")), Parenthesized(App(App(F.Id("central"), F.Id("Delta")), F.Id("k")))))))));

    private static Formula Formula36() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("k", F.Id("Nat"), Rel(App(App(F.Id("central"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("k")), Plus, Parenthesized(D(1))))), FormulaRelationOperator.Equal, App(App(F.Id("Hword"), Parenthesized(App(F.Id("Delta"), D(0)))), Parenthesized(App(App(F.Id("central"), Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("n"), Colon, F.Id("Nat"))), Sp, Mapsto, Sp, Parenthesized(App(F.Id("Delta"), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(D(1))))))))), F.Id("k"))))))));

    private static Formula Formula37() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(App(App(F.Id("muWord"), F.Id("Delta")), F.Id("n")), F.Id("w")), FormulaRelationOperator.Equal, Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("flatMap")), Parenthesized(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n"))))))))));

    private static Formula Formula38() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), All("z", App(F.Id("Fin"), F.Id("d")), Rel(App(App(App(F.Id("mu"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(D(1))))), F.Id("z")), FormulaRelationOperator.Equal, App(App(F.Id("Lword"), Parenthesized(App(F.Id("Delta"), D(0)))), Parenthesized(App(App(App(F.Id("mu"), Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("j"), Colon, F.Id("Nat"))), Sp, Mapsto, Sp, Parenthesized(App(F.Id("Delta"), Parenthesized(Seq(Parenthesized(F.Id("j")), Plus, Parenthesized(D(1))))))))), F.Id("n")), F.Id("z")))))))));

    private static Formula Formula39() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), All("k", F.Id("Nat"), Rel(App(App(F.Id("central"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(F.Id("k"))))), FormulaRelationOperator.Equal, Seq(Parenthesized(App(App(App(F.Id("muWord"), F.Id("Delta")), F.Id("n")), Parenthesized(App(App(F.Id("central"), Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("j"), Colon, F.Id("Nat"))), Sp, Mapsto, Sp, Parenthesized(App(F.Id("Delta"), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(F.Id("j"))))))))), F.Id("k"))))), Plus, Plus, Parenthesized(App(App(F.Id("central"), F.Id("Delta")), F.Id("n")))))))));

    private static Formula Formula40() =>
        All("d", F.Id("Nat"), All("source", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("target", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("f", Arrow(App(F.Id("Fin"), F.Id("d")), App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d"))))), Rel(App(App(App(F.Id("MorphicImage"), F.Id("source")), F.Id("target")), F.Id("f")), FormulaRelationOperator.Equal, Parenthesized(All("k", F.Id("Nat"), Seq(F.Id("let"), Sp, F.Id("W"), Sp, Colon, Eq, Sp, App(Seq(Parenthesized(Parenthesized(App(App(PrefixExpression(), F.Id("source")), F.Id("k")))), Dot, F.Id("flatMap")), F.Id("f")), Semi, Sp, Rel(App(App(PrefixExpression(), F.Id("target")), Seq(F.Id("W"), Dot, F.Id("length"))), FormulaRelationOperator.Equal, F.Id("W"))))))))));

    private static Formula Formula41() =>
        All("d", F.Id("Nat"), All("x", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("k", F.Id("Nat"), All("m", F.Id("Nat"), Imp(Rel(F.Id("k"), FormulaRelationOperator.LessThanOrEqual, F.Id("m")), App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), App(App(PrefixExpression(), F.Id("x")), F.Id("k")), App(App(PrefixExpression(), F.Id("x")), F.Id("m"))))))));

    private static Formula Formula42() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), App(App(App(F.Id("MorphicImage"), Parenthesized(App(F.Id("cDelta"), Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("j"), Colon, F.Id("Nat"))), Sp, Mapsto, Sp, Parenthesized(App(F.Id("Delta"), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(F.Id("j"))))))))))), Parenthesized(App(F.Id("cDelta"), F.Id("Delta")))), Parenthesized(App(App(F.Id("mu"), F.Id("Delta")), F.Id("n")))))));
}
