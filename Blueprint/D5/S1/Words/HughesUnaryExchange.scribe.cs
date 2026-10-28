using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class HughesUnaryExchangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/HughesUnaryExchange.";
    private static readonly Formula U = F.Id("u"), V = F.Id("v"), E = F.Id("E");
    private static readonly Formula M = F.Id("M"), R = F.Id("r");
    private static Formula Words => Call("List", F.Id("alpha"));
    private static Formula Nonempty(Formula w) => NotEqual(w, F.Id("nil"));
    private static Formula Unary(Formula w, string n) => Ex("a", F.Id("alpha"),
        Ex(n, Call("Nat"), And(Le(Num(1), F.Id(n)),
            Equal(w, Call("replicate", F.Id(n), F.Id("a"))))));
    private static Formula BindCommon(Formula body) => All("alpha", Call("Type"),
        All("u", Words, All("v", Words, All("E", Call("BlockCut", F.Id("alpha")),
            All("M", Call("List", F.Id("Side")), body)))));
    private static Formula Bind(Formula body) => BindCommon(All("r", Call("Nat"), body));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every minimum unary-source mask has exact descent under every admissible exchange.",
        H("Exact Native Unary Block Exchanges"), Blocks(
            Paragraph(Text("The first source is inserted and the second source is the base. "
                + "Both are nonempty. A native admissible cut exchanges two whole adjacent "
                + "maximal runs with the required exterior U-run. Either source may be unary; "
                + "the two orientations are proved with their distinct degree formulas.")),
            Describe.Lean(DescribeId.Create("exchange-lower"),
                DeclarationHandle.Create(Prefix + "exchange_lower"), H("Lower bound for every exchange"),
                StatementSource.FromAuthor(BindCommon(All("a", F.Id("alpha"), All("n", Call("Nat"),
                    Implies(And(Nonempty(U), And(Call("ValidMask", U, V, Call("original", E), M),
                        And(Call("Admissible", E, M), Or(Equal(U, Call("replicate", F.Id("n"), F.Id("a"))),
                            Equal(V, Call("replicate", F.Id("n"), F.Id("a"))))))),
                        Ex("s", Call("Nat"), Ex("t", Call("Nat"),
                            And(Equal(Call("degree", U, V, Call("original", E)), F.Id("s")),
                                And(Equal(Call("degree", U, V, Call("successor", E)), F.Id("t")),
                                    Le(F.Id("s"), Add(F.Id("t"), Num(1)))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Delete the actual block whose label belongs to the unary source. Its letters "
                    + "are all a, and the deleted word has both reduced ordered source projections. "
                    + "The old and exchanged words reinsert the same mass at two actual cuts. "
                    + "The indexed gap transport identifies the changed gap at each cut, including "
                    + "cuts separated by any number of zero-mass gaps. Adding mass increases the "
                    + "occupied-gap count by at most one; in the reverse orientation only internal "
                    + "gaps contribute. This gives the lower bound without assuming commutation "
                    + "of the non-unary projection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Every minimum mask and every exchange"), StatementSource.FromAuthor(Bind(Implies(
                    And(Nonempty(U), And(Nonempty(V), And(
                        Call("IsMinimumMask", U, V, Call("original", E), M, R),
                        And(Le(Num(2), R), And(Call("Admissible", E, M), Or(Unary(U, "m"), Unary(V, "n"))))))),
                    Equal(Call("degree", U, V, Call("successor", E)), Call("NatSub", R, Num(1)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every r>1, every minimum mask M and every admissible cut E, the successor "
                    + "degree is exactly r-1. The common-deletion lower bound gives at least r-1. "
                    + "The original native intended-successor theorem gives a valid successor mask "
                    + "with exactly r-1 U-runs and hence the matching upper bound. Both exchange "
                    + "directions are included. No choice of a preferred minimum mask is made, "
                    + "and no statement about an empty inserted source is inferred."))), DescribeRole.Theorem))));

    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Ex(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
