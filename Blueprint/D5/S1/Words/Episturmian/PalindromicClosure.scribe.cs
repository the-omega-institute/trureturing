using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Episturmian;

internal sealed class PalindromicClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Episturmian/PalindromicClosure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/droubayjustinpirello2001episturmian");
    private static readonly LibraryNoteRef Peltomaki = LibraryNoteRef.Create("D5/L/Words/peltomaki2024episturmian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Episturmian words: PalindromicClosure.", H("PalindromicClosure"),
        Blocks(
            Node("palclosure-0", "palClosure", DeclarationHandle.Create(Prefix + "palClosure"), Disp(Formula0()), "Droubay–Justin–Pirillo, Section 2: the palindromic closure construction. The evidence for the least length and its palindrome is quantified explicitly; proof irrelevance makes Classical.choose independent of these proof terms.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("palclosure-spec-1", "palClosure spec", DeclarationHandle.Create(Prefix + "palClosure_spec"), Disp(Formula1()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palcut-2", "palCut", DeclarationHandle.Create(Prefix + "palCut"), Disp(Formula2()), "The least cut leaves a palindromic suffix. Existence proof arguments are displayed as quantified evidence; proof irrelevance makes Nat.find independent of the evidence.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("palcut-spec-4", "palCut spec", DeclarationHandle.Create(Prefix + "palCut_spec"), Disp(Formula4()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palcut-min-5", "palCut min", DeclarationHandle.Create(Prefix + "palCut_min"), Disp(Formula5()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palindrome-extension-middle-6", "palindrome extension middle", DeclarationHandle.Create(Prefix + "palindrome_extension_middle"), Disp(Formula6()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palindrome-extension-length-7", "palindrome extension length", DeclarationHandle.Create(Prefix + "palindrome_extension_length"), Disp(Formula7()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("closure-candidate-palindrome-8", "closure candidate palindrome", DeclarationHandle.Create(Prefix + "closure_candidate_palindrome"), Disp(Formula8()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("palclosure-formula-cut-9", "palClosure formula cut", DeclarationHandle.Create(Prefix + "palClosure_formula_cut"), Disp(Formula9()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("central-10", "central", DeclarationHandle.Create(Prefix + "central"), Disp(Formula10()), "Droubay–Justin–Pirillo, Section 2: the palindromic closure construction.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("central-length-ge-11", "central length ge", DeclarationHandle.Create(Prefix + "central_length_ge"), Disp(Formula11()), "The displayed statement gives the complete hypotheses and conclusion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("cdelta-12", "cDelta", DeclarationHandle.Create(Prefix + "cDelta"), Disp(Formula12()), "Droubay–Justin–Pirillo, Section 2: the palindromic closure construction. The Fin index shows its value; its inequality proof is implicit.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lang-13", "Lang", DeclarationHandle.Create(Prefix + "Lang"), Disp(Formula13()), "Peltomäki, Section 2: episturmian words, directive words and partial quotients.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Peltomaki)),
            Node("boundedpq-15", "BoundedPQ", DeclarationHandle.Create(Prefix + "BoundedPQ"), Disp(Formula15()), "Peltomäki, Section 2: episturmian words, directive words and partial quotients.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Peltomaki)),
            Node("fractionalpower-17", "fractionalPower", DeclarationHandle.Create(Prefix + "fractionalPower"), Disp(Formula17()), "The displayed equations define the object. The Fin index shows its value; its inequality proof is implicit. Nat.mod(i, q) denotes the natural-number remainder i % q.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("dioadmissible-18", "DioAdmissible", DeclarationHandle.Create(Prefix + "DioAdmissible"), Disp(Formula18()), "Peltomäki, Definition 1.1.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Peltomaki)),
            Node("dio-19", "dio", DeclarationHandle.Create(Prefix + "dio"), Disp(Formula19()), "Peltomäki, Definition 1.1.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Peltomaki)),
            Node("claim-20", "claim", DeclarationHandle.Create(Prefix + "claim"), Disp(Formula20()), "Peltomäki, Conjecture 8.4, Section 8.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Peltomaki)))));

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

    private static Formula AperiodicityFormula() => Seq(Neg, Sp, Parenthesized(Ex("N", F.Id("Nat"), Ex("p", F.Id("Nat"), And(Rel(D(0), FormulaRelationOperator.LessThan, F.Id("p")), All("n", F.Id("Nat"), Imp(Rel(F.Id("N"), FormulaRelationOperator.LessThanOrEqual, F.Id("n")), Rel(App(F.Id("t"), Parenthesized(Seq(F.Id("n"), Plus, F.Id("p")))), FormulaRelationOperator.Equal, App(F.Id("t"), F.Id("n"))))))))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Arrow(Formula left, Formula right) => Parenthesized(new Formula.TypeArrow(Parenthesized(left), Parenthesized(right)));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Parenthesized(type), body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Parenthesized(type), body);

    private static Formula Formula0() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("h", Ex("n", F.Id("Nat"), Ex("p", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), And(App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), F.Id("w"), F.Id("p")), And(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("p")), Rel(Seq(F.Id("p"), Dot, F.Id("length")), FormulaRelationOperator.Equal, F.Id("n")))))), All("hp", Ex("p", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), And(App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), F.Id("w"), F.Id("p")), And(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("p")), Rel(Seq(F.Id("p"), Dot, F.Id("length")), FormulaRelationOperator.Equal, App(Seq(F.Id("Nat"), Dot, F.Id("find")), F.Id("h")))))), Rel(App(F.Id("palClosure"), F.Id("w")), FormulaRelationOperator.Equal, App(Seq(F.Id("Classical"), Dot, F.Id("choose")), F.Id("hp")))))));

    private static Formula Formula1() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), And(App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), F.Id("w"), App(F.Id("palClosure"), F.Id("w"))), And(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), Parenthesized(App(F.Id("palClosure"), F.Id("w")))), All("p", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), F.Id("w"), F.Id("p")), Imp(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("p")), Rel(Seq(Parenthesized(Parenthesized(App(F.Id("palClosure"), F.Id("w")))), Dot, F.Id("length")), FormulaRelationOperator.LessThanOrEqual, Seq(F.Id("p"), Dot, F.Id("length"))))))))));

    private static Formula Formula2() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("h", Ex("k", F.Id("Nat"), And(Rel(F.Id("k"), FormulaRelationOperator.LessThanOrEqual, Seq(F.Id("w"), Dot, F.Id("length"))), App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("drop")), F.Id("k")))))), Rel(App(F.Id("palCut"), F.Id("w")), FormulaRelationOperator.Equal, App(Seq(F.Id("Nat"), Dot, F.Id("find")), F.Id("h"))))));

    private static Formula Formula4() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), And(Rel(App(F.Id("palCut"), F.Id("w")), FormulaRelationOperator.LessThanOrEqual, Seq(F.Id("w"), Dot, F.Id("length"))), App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("drop")), Parenthesized(App(F.Id("palCut"), F.Id("w")))))))));

    private static Formula Formula5() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("k", F.Id("Nat"), Imp(Rel(F.Id("k"), FormulaRelationOperator.LessThanOrEqual, Seq(F.Id("w"), Dot, F.Id("length"))), Imp(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("drop")), F.Id("k")))), Rel(App(F.Id("palCut"), F.Id("w")), FormulaRelationOperator.LessThanOrEqual, F.Id("k")))))));

    private static Formula Formula6() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("r", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), Parenthesized(Seq(Parenthesized(F.Id("w")), Plus, Plus, Parenthesized(F.Id("r"))))), Imp(Rel(Seq(F.Id("r"), Dot, F.Id("length")), FormulaRelationOperator.LessThanOrEqual, Seq(F.Id("w"), Dot, F.Id("length"))), App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("drop")), Seq(F.Id("r"), Dot, F.Id("length"))))))))));

    private static Formula Formula7() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("p", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Imp(App(Seq(F.Id("List"), Dot, F.Id("IsPrefix")), F.Id("w"), F.Id("p")), Imp(App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), F.Id("p")), Rel(Seq(Parenthesized(Seq(F.Id("w"), Dot, F.Id("length"))), Plus, Parenthesized(App(F.Id("palCut"), F.Id("w")))), FormulaRelationOperator.LessThanOrEqual, Seq(F.Id("p"), Dot, F.Id("length"))))))));

    private static Formula Formula8() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), App(Seq(F.Id("List"), Dot, F.Id("Palindrome")), Parenthesized(Seq(Parenthesized(F.Id("w")), Plus, Plus, Parenthesized(Seq(Parenthesized(Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("take")), Parenthesized(App(F.Id("palCut"), F.Id("w")))))), Dot, F.Id("reverse"))))))));

    private static Formula Formula9() =>
        All("d", F.Id("Nat"), All("w", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Rel(App(F.Id("palClosure"), F.Id("w")), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("w")), Plus, Plus, Parenthesized(Seq(Parenthesized(Parenthesized(App(Seq(F.Id("w"), Dot, F.Id("take")), Parenthesized(App(F.Id("palCut"), F.Id("w")))))), Dot, F.Id("reverse")))))));

    private static Formula Formula10() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), And(Rel(App(App(F.Id("central"), F.Id("Delta")), Parenthesized(D(0))), FormulaRelationOperator.Equal, Seq(OpenBracket, CloseBracket)), All("k", F.Id("Nat"), Rel(App(App(F.Id("central"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("k")), Plus, Parenthesized(D(1))))), FormulaRelationOperator.Equal, App(F.Id("palClosure"), Parenthesized(Seq(Parenthesized(App(App(F.Id("central"), F.Id("Delta")), F.Id("k"))), Plus, Plus, Parenthesized(Seq(OpenBracket, App(F.Id("Delta"), F.Id("k")), CloseBracket))))))))));

    private static Formula Formula11() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("k", F.Id("Nat"), Rel(F.Id("k"), FormulaRelationOperator.LessThanOrEqual, Seq(Parenthesized(Parenthesized(App(App(F.Id("central"), F.Id("Delta")), F.Id("k")))), Dot, F.Id("length"))))));

    private static Formula Formula12() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("n", F.Id("Nat"), Rel(App(App(F.Id("cDelta"), F.Id("Delta")), F.Id("n")), FormulaRelationOperator.Equal, App(Seq(Parenthesized(Parenthesized(App(App(F.Id("central"), F.Id("Delta")), Parenthesized(Seq(Parenthesized(F.Id("n")), Plus, Parenthesized(D(1))))))), Dot, F.Id("get")), Seq(Langle, Sp, F.Id("n"), Rangle, Sp))))));

    private static Formula Formula13() =>
        All("d", F.Id("Nat"), All("x", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), Rel(App(F.Id("Lang"), F.Id("x")), FormulaRelationOperator.Equal, Parenthesized(Seq(OpenBrace, Sp, F.Id("w"), Colon, App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Sp, Mid, Sp, Ex("i", F.Id("Nat"), All("j", App(F.Id("Fin"), Seq(F.Id("w"), Dot, F.Id("length"))), Rel(App(Seq(F.Id("w"), Dot, F.Id("get")), F.Id("j")), FormulaRelationOperator.Equal, App(F.Id("x"), Parenthesized(Seq(Parenthesized(F.Id("i")), Plus, Parenthesized(Call("val", F.Id("j"))))))))), Sp, CloseBrace)))));


    private static Formula Formula15() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), Rel(App(F.Id("BoundedPQ"), F.Id("Delta")), FormulaRelationOperator.Equal, Parenthesized(Ex("B", F.Id("Nat"), All("i", F.Id("Nat"), Ex("j", F.Id("Nat"), And(Rel(F.Id("j"), FormulaRelationOperator.LessThan, F.Id("B")), Rel(App(F.Id("Delta"), Parenthesized(Seq(Parenthesized(F.Id("i")), Plus, Parenthesized(F.Id("j"))))), FormulaRelationOperator.NotEqual, App(F.Id("Delta"), F.Id("i")))))))))));


    private static Formula Formula17() =>
        All("d", F.Id("Nat"), All("V", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), All("hV", Rel(F.Id("V"), FormulaRelationOperator.NotEqual, Seq(OpenBracket, CloseBracket)), All("ell", F.Id("Nat"), Rel(App(App(App(F.Id("fractionalPower"), F.Id("V")), F.Id("hV")), F.Id("ell")), FormulaRelationOperator.Equal, App(Seq(Parenthesized(Parenthesized(App(Seq(F.Id("List"), Dot, F.Id("range")), F.Id("ell")))), Dot, F.Id("map")), Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("i"), Colon, F.Id("Nat"))), Sp, Mapsto, Sp, Parenthesized(App(Seq(F.Id("V"), Dot, F.Id("get")), Seq(Langle, Sp, App(Seq(F.Id("Nat"), Dot, F.Id("mod")), F.Id("i"), Seq(F.Id("V"), Dot, F.Id("length"))), Rangle, Sp)))))))))));

    private static Formula Formula18() =>
        All("d", F.Id("Nat"), All("x", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("rho", F.Id("NNReal"), Rel(App(App(F.Id("DioAdmissible"), F.Id("x")), F.Id("rho")), FormulaRelationOperator.Equal, Parenthesized(All("L", F.Id("Nat"), Ex("U", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Ex("V", App(F.Id("List"), Parenthesized(App(F.Id("Fin"), F.Id("d")))), Ex("ell", F.Id("Nat"), Ex("hV", Rel(F.Id("V"), FormulaRelationOperator.NotEqual, Seq(OpenBracket, CloseBracket)), And(Rel(Seq(F.Id("V"), Dot, F.Id("length")), FormulaRelationOperator.LessThanOrEqual, F.Id("ell")), And(Rel(Seq(Parenthesized(Seq(F.Id("U"), Dot, F.Id("length"))), Plus, Parenthesized(F.Id("ell"))), FormulaRelationOperator.GreaterThanOrEqual, F.Id("L")), And(Rel(App(App(PrefixExpression(), F.Id("x")), Parenthesized(Seq(Parenthesized(Seq(F.Id("U"), Dot, F.Id("length"))), Plus, Parenthesized(F.Id("ell"))))), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("U")), Plus, Plus, Parenthesized(App(App(App(F.Id("fractionalPower"), F.Id("V")), F.Id("hV")), F.Id("ell"))))), Rel(Seq(Parenthesized(Parenthesized(Parenthesized(Seq(Seq(Parenthesized(Seq(F.Id("U"), Dot, F.Id("length"))), Plus, Parenthesized(F.Id("ell"))), Colon, F.Id("Real"))))), Slash, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(F.Id("U"), Dot, F.Id("length"))), Plus, Parenthesized(Seq(F.Id("V"), Dot, F.Id("length"))))))), FormulaRelationOperator.GreaterThanOrEqual, Parenthesized(Parenthesized(Seq(F.Id("rho"), Colon, F.Id("Real"))))))))))))))))));

    private static Formula Formula19() =>
        All("d", F.Id("Nat"), All("x", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), Rel(App(F.Id("dio"), F.Id("x")), FormulaRelationOperator.Equal, Parenthesized(App(F.Id("iSup"), Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("rho"), Colon, F.Id("NNReal"))), Sp, Mapsto, Sp, Parenthesized(App(F.Id("iSup"), Seq(F.Id("fun"), Sp, Parenthesized(Seq(Cdot, Sp, Colon, App(App(F.Id("DioAdmissible"), F.Id("x")), F.Id("rho")))), Sp, Mapsto, Sp, Parenthesized(Parenthesized(Parenthesized(Seq(F.Id("rho"), Colon, F.Id("ENNReal"))))))))))))));

    private static Formula Formula20() =>
        Rel(F.Id("claim"), FormulaRelationOperator.Equal, Parenthesized(All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("t", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), Imp(Rel(App(F.Id("Lang"), F.Id("t")), FormulaRelationOperator.Equal, App(F.Id("Lang"), Parenthesized(App(F.Id("cDelta"), F.Id("Delta"))))), Imp(AperiodicityFormula(), Parenthesized(Iff(Rel(App(F.Id("dio"), F.Id("t")), FormulaRelationOperator.LessThan, Infty), App(F.Id("BoundedPQ"), F.Id("Delta")))))))))));
}
