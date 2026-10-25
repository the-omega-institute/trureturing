using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class BlockGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native legal-word quadratic loads have a finite growth constant with matching infimum and supremum formulas.",
        H("Legal-word block growth"),
        Blocks(
            Paragraph(Text(
                "For each natural length n, legalWordGraph(n) has all Boolean words of length n "
                + "with no adjacent ones as vertices, and joins words differing at exactly one position. "
                + "Write K(n)=kappa(legalWordGraph(n)), using the actual infimum over feasible "
                + "quadratic edge allocations. The empty word is the sole vertex at length zero.")),
            Describe.Lean(DescribeId.Create("native-growth-constant"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LegalWords/BlockGrowth.growth_constant"),
                H("Near additivity and the common growth constant"),
                StatementSource.FromAuthor(GrowthFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Splitting a word of length n+m into its first n and last m letters is an "
                        + "injective adjacency-preserving map into the Cartesian graph. Conversely, "
                        + "inserting one zero between two legal words gives an injective "
                        + "adjacency-preserving map from that Cartesian graph into the length n+m+1 "
                        + "graph. These maps are defined at zero lengths as well. Applying native "
                        + "injective transport and Cartesian additivity proves both inequalities. "
                        + "There are no edges at length zero, so K(0)=0; all native loads are nonnegative.")),
                    Paragraph(Text(
                        "Pinned Fekete convergence for the subadditive sequence K gives a finite "
                        + "real limit c and the infimum over n at least one. The estimate K(n) at most "
                        + "n K(1) bounds the ratios of u(j)=-K(j-1) below. The right block inequality "
                        + "makes u subadditive, including j=0. A second application of Fekete, "
                        + "together with n/(n+1) tending to one, identifies its limit as -c. "
                        + "Thus every K(n)/(n+1) is at most c, while these ratios converge to c, "
                        + "so their supremum is c. The infimum and supremum bounds give the "
                        + "two linear estimates for every natural n, including zero. "
                        + "No positive-mass restriction or auxiliary optimization is substituted "
                        + "for the native graph infimum."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula K(Formula n) => Call("kappa", Call("legalWordGraph", n));

    private static Formula GrowthFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), c = F.Id("c"), nat = Call("Nat");
        Formula ratio = Lambda("n", nat, Div(K(n), Call("castReal", n)));
        Formula shifted = Lambda("n", nat, Div(K(n), Add(Call("castReal", n), D(1))));
        Formula near = All("n", nat, All("m", nat,
            And(Le(K(Add(n, m)), Add(K(n), K(m))), Le(Add(K(n), K(m)), K(Add(Add(n, m), D(1)))))));
        Formula extrema = And(Eq(c, Call("sInf", Call("image", Par(ratio), Call("Ici", D(1))))),
            Eq(c, Call("sSup", Call("range", Par(shifted)))));
        Formula brackets = All("n", nat, And(Le(Mul(c, Call("castReal", n)), K(n)),
            Le(K(n), Mul(c, Add(Call("castReal", n), D(1))))));
        return Disp(And(Eq(K(D(0)), D(0)), And(near, Ex("c", Call("Real"),
            And(Call("Tendsto", Par(ratio), Call("atTop"), Call("nhds", c)), And(extrema, brackets))))));
    }
}
