using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RestrictedSchur;

internal sealed class RestrictedSchurDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/gaiser2026restrictedschur");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricted generalized Schur numbers and the eventual equality in Open Question 6.2 of Gaiser.",
        H("Restricted Generalized Schur Numbers"),
        Blocks(
            Node("monochromatic-solution", "Monochromatic solutions with a prescribed number of distinct values",
                "HasMonochromaticSolution", SolutionFormula(),
                "A colouring c maps the natural numbers to Fin(r); only its values from 1 through n matter. "
                    + "The tuple x has k summands and a final value equal to their sum. Every entry lies "
                    + "between 1 and n, the image of the tuple has exactly l+1 elements, and all entries "
                    + "have the same colour. Repeated summands are permitted.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("restricted-schur-number", "The restricted generalized Schur number", "schur", SchurFormula(),
                "The number S_r(k;l) is the infimum in the natural numbers of the set of n for which "
                    + "every r-colouring has such a solution. If this set is nonempty, the infimum is its "
                    + "least element; the infimum of the empty set is zero. Gaiser's definition concerns k at least 2.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("eventual-equality", "The equality proposed in Open Question 6.2", "claim", ClaimFormula(),
                "The proposed equality asserts the existence of a natural threshold K such that "
                    + "S_3(k;2) equals k^3+3k^2+k-1 for every natural k at least K. "
                    + "The subtraction in this expression is natural-number subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SolutionFormula()
    {
        var indices = Call("Fin", Add(F.Id("k"), D(1)));
        var bounds = All("i", indices,
            And(Le(D(1), Call("x", F.Id("i"))), Le(Call("x", F.Id("i")), F.Id("n"))));
        var sum = Seq(Sum, Sp, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp,
            Call("Fin", F.Id("k"))), Sp, Call("x", Call("castSucc", F.Id("i"))));
        var equation = Equal(sum, Call("x", Call("last", F.Id("k"))));
        var distinct = Equal(Call("card", Call("image", F.Id("x"), Call("univ", indices))),
            Add(F.Id("l"), D(1)));
        var colours = All("i", indices, All("j", indices,
            Equal(Call("c", Call("x", F.Id("i"))), Call("c", Call("x", F.Id("j"))))));
        return Disp(IffFormula(Call("HasMonochromaticSolution", F.Id("r"), F.Id("k"),
            F.Id("l"), F.Id("n"), F.Id("c")), Some("x", Seq(indices, Sp, To, Sp, F.Id("Nat")),
                And(bounds, And(equation, And(distinct, colours))))));
    }

    private static Formula SchurFormula() => Disp(Equal(
        Call("schur", F.Id("r"), F.Id("k"), F.Id("l")),
        Call("sInf", Seq(OpenBrace, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Sp, Mid, Sp,
            All("c", Seq(F.Id("Nat"), Sp, To, Sp, Call("Fin", F.Id("r"))),
                Call("HasMonochromaticSolution", F.Id("r"), F.Id("k"), F.Id("l"), F.Id("n"), F.Id("c"))),
            Sp, CloseBrace, Sp))));

    private static Formula ClaimFormula() => Disp(IffFormula(F.Id("claim"),
        Some("K", F.Id("Nat"), All("k", F.Id("Nat"),
            ImpliesFormula(Le(F.Id("K"), F.Id("k")), Equal(Call("schur", D(3), F.Id("k"), D(2)),
                Seq(F.Id("k"), Caret, Grp(D(3)), Sp, Plus, Sp, D(3), Sp, Cdot, Sp,
                    F.Id("k"), Caret, Grp(D(2)), Sp, Plus, Sp, F.Id("k"), Sp, Minus, Sp, D(1))))))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
}
