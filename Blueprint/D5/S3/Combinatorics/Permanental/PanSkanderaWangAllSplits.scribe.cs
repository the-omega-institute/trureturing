using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-split permanental inequality for totally nonnegative real matrices.",
        H("PanSkanderaWangAllSplits"),
        Blocks(
            Node("claim", "claim", "claim",
                claimFormula(),
                ClaimProse(),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", "result",
                resultFormula(),
                "Every real TNN matrix of order at least two satisfies the quoted inequality at each split between one and n-1. The balanced pairing argument, left identity padding and simultaneous reversal give the full range.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("psw-all-split-permanental-inequality"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula claimFormula() => Disp(
        Equal(F.Id("claim"), All("n", Naturals(), Implies(LessEqual(D(2), F.Id("n")), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), Implies(Call("TNN", F.Id("A")), All("h", Naturals(), Implies(LessEqual(D(1), F.Id("h")), Implies(LessEqual(F.Id("h"), Subtract(F.Id("n"), D(1))), LessEqual(Multiply(Call("principalPermanent", F.Id("A"), Call("evenIndices", F.Id("n"))), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, Call("evenIndices", F.Id("n"))))), Multiply(Call("principalPermanent", F.Id("A"), Call("prefixIndices", F.Id("n"), F.Id("h"))), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, Call("prefixIndices", F.Id("n"), F.Id("h")))))))))))))));

    private static Formula resultFormula() => Disp(
        All("n", Naturals(), Implies(LessEqual(D(2), F.Id("n")), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), Implies(Call("TNN", F.Id("A")), All("h", Naturals(), Implies(LessEqual(D(1), F.Id("h")), Implies(LessEqual(F.Id("h"), Subtract(F.Id("n"), D(1))), LessEqual(Multiply(Call("principalPermanent", F.Id("A"), Call("evenIndices", F.Id("n"))), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, Call("evenIndices", F.Id("n"))))), Multiply(Call("principalPermanent", F.Id("A"), Call("prefixIndices", F.Id("n"), F.Id("h"))), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, Call("prefixIndices", F.Id("n"), F.Id("h"))))))))))))));

    private static BlockSequence ClaimProse() => Blocks(Paragraph(
        Text("Source (EPTCS 445, p. 139, abstract): “We also conjecture the inequalities (∗) to hold for all TNN matrices and all h = 1, …, n−1.” Section 1 (p. 140): “We conjecture the inequalities to hold for all totally nonnegative matrices and I = [h].” Mathematical glyphs and whitespace follow the displayed source; the prose is verbatim. Lean uses zero-based Fin indices and the paper uses one-based indices. TNN quantifies over every increasing square-minor selection. Each principal permanent is Mathlib Matrix.permanent, with the empty-block permanent equal to one.")));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, BlockSequence prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, prose, role);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Sp, Grp(F.Id("R")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
