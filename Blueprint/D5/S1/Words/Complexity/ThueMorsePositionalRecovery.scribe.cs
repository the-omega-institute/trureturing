using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class ThueMorsePositionalRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/ThueMorsePositionalRecovery.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/rigostipulantiwhiteland2022binomial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.",
        H("Thue Morse Positional Recovery"), Blocks(
            Node("core_last_strict", "core last strict",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("k"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, OpenBrace, Seq(Operatorname, Grp(F.Id("n"))), Sp, Bar, Sp, Seq(Operatorname, Grp(F.Id("binomialComplexity"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("core"))), Sp, Seq(Operatorname, Grp(F.Id("k"))))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("k"))), Sp, Plus, Sp, D(1))), Sp, Seq(Operatorname, Grp(F.Id("n"))), Sp, Lt, Sp, Seq(Operatorname, Grp(F.Id("binomialComplexity"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("core"))), Sp, Seq(Operatorname, Grp(F.Id("k"))))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("k"))), Sp, Plus, Sp, D(2))), Sp, Seq(Operatorname, Grp(F.Id("n"))), CloseBrace, Dot, Seq(Operatorname, Grp(F.Id("Infinite"))))),
                "Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("core_as_expansion", "core as expansion",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("r"))), Sp, Seq(Operatorname, Grp(F.Id("k"))), Sp, Colon, Sp, Seq(Operatorname, Grp(F.Id("Nat"))))), Comma, Sp, Seq(Operatorname, Grp(F.Id("core"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("r"))), Sp, Plus, Sp, Seq(Operatorname, Grp(F.Id("k"))))), Sp, Eq, Sp, Seq(Operatorname, Grp(F.Id("uniformExpansion"))), Sp, Parenthesized(Seq(D(2), Sp, Caret, Grp(Seq(Seq(Operatorname, Grp(F.Id("r"))))))), Sp, Parenthesized(Seq(F.Id("Nat"), Dot, F.Id("two"), Underscore, Grp(Seq(F.Id("pow"), Underscore, Grp(F.Id("pos")))), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("fun"))), Sp, Seq(Operatorname, Grp(F.Id("a"))), Sp, Seq(Operatorname, Grp(F.Id("i"))), Sp, Mapsto, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Dot, Seq(Operatorname, Grp(F.Id("xor"))), Sp, Seq(Operatorname, Grp(F.Id("a"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("thueMorse"))), Sp, Call("val", F.Id("i")))))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("core"))), Sp, Seq(Operatorname, Grp(F.Id("k"))))))),
                "The expansion uses the Fin-to-Nat value of each block index. The subscripted positivity proof spells the Lean constant Nat.two_pow_pos and introduces no new abbreviation.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("core_middle_strict", "core middle strict",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("k"))), Sp, Seq(Operatorname, Grp(F.Id("j"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, D(2), Sp, Leq, Sp, Seq(Operatorname, Grp(F.Id("j"))), Sp, To, Sp, Seq(Operatorname, Grp(F.Id("j"))), Sp, Leq, Sp, Seq(Operatorname, Grp(F.Id("k"))), Sp, To, Sp, OpenBrace, Seq(Operatorname, Grp(F.Id("n"))), Sp, Bar, Sp, Seq(Operatorname, Grp(F.Id("binomialComplexity"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("core"))), Sp, Seq(Operatorname, Grp(F.Id("k"))))), Sp, Seq(Operatorname, Grp(F.Id("j"))), Sp, Seq(Operatorname, Grp(F.Id("n"))), Sp, Lt, Sp, Seq(Operatorname, Grp(F.Id("binomialComplexity"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("core"))), Sp, Seq(Operatorname, Grp(F.Id("k"))))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("j"))), Sp, Plus, Sp, D(1))), Sp, Seq(Operatorname, Grp(F.Id("n"))), CloseBrace, Dot, Seq(Operatorname, Grp(F.Id("Infinite"))))),
                "Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("Rigidity.top_profile_injectivity", "top profile injectivity",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("k"))), Sp, Seq(Operatorname, Grp(F.Id("n"))), Sp, Colon, Sp, Seq(Operatorname, Grp(F.Id("Nat"))))), Comma, Sp, Seq(Operatorname, Grp(F.Id("Set"))), Dot, Seq(Operatorname, Grp(F.Id("InjOn"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("binomialProfile"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("k"))), Sp, Plus, Sp, D(2))))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("wordFactorSet"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("core"))), Sp, Seq(Operatorname, Grp(F.Id("k"))))), Sp, Seq(Operatorname, Grp(F.Id("n"))), Sp, Colon, Sp, Seq(Operatorname, Grp(F.Id("Set"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("Fin"))), Sp, Seq(Operatorname, Grp(F.Id("n"))), Sp, To, Sp, Seq(Operatorname, Grp(F.Id("Bool"))))))))),
                "Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
