using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class PrefixReversalStarCardinalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversalStarCardinality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit cyclic-action coordinates give the residual zero-star its exact finite cardinality.",
        H("Residual Zero-Star Cardinality"),
        Blocks(
            Paragraph(Text(
                "For a configuration z with the marked label at the final position, the residual zero-star "
                + "is the independently defined set of configurations whose deletion is the residual circle "
                + "of z in either orientation. The coordinate bijection separates the orientation bit, the "
                + "global rotation, and the rotation of the first m positions.")),
            Paragraph(Text(
                "There are m choices for the first-position rotation, m+1 choices for the global rotation, "
                + "and two choices for the residual orientation. Hence the exact vertex count is "
                + "2m(m+1), which is the finite layer cardinality used by the native Hamilton construction.")),
            Describe.Lean(DescribeId.Create("star-cardinality"),
                DeclarationHandle.Create(Prefix + "star_cardinality"),
                H("Exact Residual Star Cardinality"),
                StatementSource.FromAuthor(CardinalityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m at least three and every configuration z, the finite subtype "
                    + "of the residual zero-star has cardinality m times (m+1) times 2."))),
                DescribeRole.Theorem))));

    private static Formula CardinalityFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z");
        Formula n = Add(m, D(1));
        Formula configuration = Call("Configuration", m);
        Formula marked = Call("apply", z, Call("last", m));
        Formula residual = Call("residualList", z);
        Formula star = Call("Star", marked, residual, F.Id("v"));
        Formula subtype = Call("Subtype", configuration, star);
        Formula card = Call("Fintype.card", subtype);
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            All("z", configuration, Eq(card, Mul(Mul(m, n), D(2)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
    private static Formula Mul(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Multiply, r);
}
