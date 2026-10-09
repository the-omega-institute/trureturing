using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ErdosUlam;

internal sealed class SublatticeRankRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ErdosUlam/SublatticeRankRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A colouring attaining the trivial monochromatic chain bound in an odd Boolean lattice "
            + "is constant on each rank, and its ranks split equally between the two colours.",
        H("Rank rigidity from a sharp chain bound"),
        Blocks(
            Node("rank-rigidity", "Equal-rank sets have equal colours", "rank_rigidity",
                RigidityFormula(),
                "Every maximal chain has n plus one members. Its two colour classes are "
                    + "sublattices whenever nonempty, so the assumed upper bound forces each "
                    + "colour to occur exactly (n plus one) divided by two times. For a set C "
                    + "and distinct points x and y outside C, enumerate C first, then x and y, "
                    + "then the remaining points. Reversing x and y produces two maximal chains "
                    + "which differ only at rank |C| plus one. Balance forces C union {x} and "
                    + "C union {y} to have the same colour. For equal-size A and B, choose "
                    + "x in A outside B and y in B outside A and exchange them. The number "
                    + "of points of A outside B decreases by one. Induction connects A to B.",
                DescribeRole.Theorem),
            Node("balanced-prefixes", "The prefix ranks split equally", "balanced_prefixes",
                BalancedFormula(),
                "The standard prefix chain consists of the subsets with elements less "
                    + "than r, for r from zero through n. Distinct ranks give distinct sets. "
                    + "The assumed upper bound applies to either colour class of this chain. "
                    + "Their cardinalities sum to the even number n plus one, and neither "
                    + "exceeds half that number, so both equal half.",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Bool() => new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
    private static Formula Sets(Formula n) => Call("Finset", Call("Fin", n));
    private static Formula Families(Formula n) => Call("Finset", Sets(n));
    private static Formula Colourings(Formula n) => new Formula.TypeArrow(Sets(n), Bool());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Half(Formula n) =>
        new Formula.Floor(new Formula.Fraction(Add(n, D(1)), D(2)));
    private static Formula Small(Formula n, Formula chi) =>
        All("L", Families(n), Imp(Call("IsSublattice", F.Id("L")),
            Imp(Call("Monochromatic", chi, F.Id("L")), Leq(Call("card", F.Id("L")), Half(n)))));

    private static Formula RigidityFormula()
    {
        var n = F.Id("n"); var chi = F.Id("chi"); var a = F.Id("A"); var b = F.Id("B");
        var equalRanks = All("A", Sets(n), All("B", Sets(n),
            Imp(Eqn(Call("card", a), Call("card", b)), Eqn(Call("chi", a), Call("chi", b)))));
        return Disp(All("n", Nat(), Imp(Call("Odd", n), All("chi", Colourings(n),
            Imp(Small(n, chi), equalRanks)))));
    }

    private static Formula BalancedFormula()
    {
        var n = F.Id("n"); var chi = F.Id("chi"); var c = F.Id("c"); var r = F.Id("r");
        var predicate = Seq(LambdaLower, Seq(Open, r, Colon, Sp, Nat(), Close), Sp,
            Eqn(Call("chi", Call("initialSegment", n, r)), c));
        var count = Call("card", Call("filter", Call("range", Add(n, D(1))), predicate));
        return Disp(All("n", Nat(), Imp(Call("Odd", n), All("chi", Colourings(n),
            Imp(Small(n, chi), All("c", Bool(), Eqn(count, Half(n))))))));
    }
}
