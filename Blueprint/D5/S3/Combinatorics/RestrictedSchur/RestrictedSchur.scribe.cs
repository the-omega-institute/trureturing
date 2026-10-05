using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RestrictedSchur;

internal sealed class RestrictedSchurDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/gaiser2026restrictedschur");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A seven-block three-colouring gives a negative answer to Open Question 6.2 of Gaiser.",
        H("A Seven-Block Colouring Refutes the Proposed Eventual Equality"),
        Blocks(
            Node("seven-block-colouring", "The seven-block three-colouring", "sevenBlockColouring",
                ColouringFormula(),
                "For integer k and n, the conditions in the nested conditional are evaluated in order; "
                    + "ite selects its second argument when its first argument holds, and its third otherwise. "
                    + "For k at least 3, the seven consecutive blocks in the positive integers have colours "
                    + "0, 1, 0, 2, 0, 1, 0. The first six right endpoints are k, k^2+k, k^2+2k-1, "
                    + "k^3+2k^2, k^3+2k^2+k-1, and k^3+3k^2+k-2; all larger integers have colour 0.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("seven-block-avoidance", "Absence of three-value monochromatic solutions", "sevenBlock_avoids",
                AvoidanceFormula(),
                "For every natural k at least 3, the interval from 1 through k^3+3k^2+2k-3 "
                    + "contains no monochromatic solution with exactly three distinct values under this colouring. "
                    + "The positive summands are smaller than their sum, so a putative solution has exactly "
                    + "two summand values a<b, with multiplicities j and k-j for 1 at most j less than k. "
                    + "For each pair of blocks of the same colour, interval inequalities place "
                    + "ja+(k-j)b in a different colour or beyond the interval.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("eventual-equality-refuted", "Open Question 6.2 has a negative answer", "result",
                Disp(new Formula.Not(Seq(Open, F.Id("claim"), Close))),
                "There is no natural threshold after which S_3(k;2) always equals k^3+3k^2+k-1. "
                    + "Given a proposed threshold K, take k=max(K,3). The proposed value is positive, "
                    + "so equality would make the set defining the Schur number nonempty and put its "
                    + "least element in that set. The seven-block colouring would then have a solution "
                    + "in the proposed interval. That interval is contained in the larger interval "
                    + "from the preceding theorem, contradicting the absence of such a solution. "
                    + "Here claim denotes the eventual equality defined in RestrictedSchurDefs.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

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

    private static Formula ColouringFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var square = new Formula.Power(k, D(2));
        var cube = new Formula.Power(k, D(3));
        var central = Add(cube, Mul(D(2), square));
        var value = Call("ite", Le(n, k), D(0),
            Call("ite", Le(n, Add(square, k)), D(1),
                Call("ite", Le(n, Sub(Add(square, Mul(D(2), k)), D(1))), D(0),
                    Call("ite", Le(n, central), D(2),
                        Call("ite", Le(n, Sub(Add(central, k), D(1))), D(0),
                            Call("ite", Le(n, Sub(Add(Add(cube, Mul(D(3), square)), k), D(2))), D(1), D(0)))))));
        return Disp(Equal(Call("sevenBlockColouring", k, n), value));
    }

    private static Formula AvoidanceFormula()
    {
        var k = F.Id("k");
        var upper = Sub(Add(Add(new Formula.Power(k, D(3)), Mul(D(3), new Formula.Power(k, D(2)))),
            Mul(D(2), k)), D(3));
        var colouring = Seq(F.Id("n"), Sp, Mapsto, Sp, Call("sevenBlockColouring", k, F.Id("n")));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"), F.Id("Nat"),
            new Formula.Logic(Le(D(3), k), FormulaLogicOperator.Implies,
                new Formula.Not(Seq(Open, Call("HasMonochromaticSolution", D(3), k, D(2), upper, colouring), Close)))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
