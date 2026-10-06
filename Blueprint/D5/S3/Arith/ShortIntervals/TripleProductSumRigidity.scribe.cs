using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ShortIntervals;

internal sealed class TripleProductSumRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal triple products in a sufficiently short positive integer interval have equal sums.",
        H("Triple-product sum rigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("triple-product-sum-rigidity"),
            DeclarationHandle.Create("D5/S3/Arith/ShortIntervals/TripleProductSumRigidity.triple_product_sum_rigidity"),
            H("Integer sum rigidity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("All eight variables are integers. Each of the six rows lies in the same "
                    + "closed interval. Repetitions, shared rows and arbitrary row order are allowed; "
                    + "the equality of sums is a conclusion.")),
                Paragraph(Text("Choose a least member x of each triple and write the other members as "
                    + "x+r and x+s. The cubic defect is 9x(r^2-rs+s^2)+(r+s)^3. "
                    + "For positive width it lies between zero and 9mh^2+17h^3, strictly below "
                    + "26m^2. Distinct integer sums at least 3m have cube difference greater than "
                    + "27m^2. Equal products make that cube difference a difference of defects, "
                    + "which is impossible. At zero width every row equals m.")),
                Paragraph(Text("The stronger predicate m>(h+1)^2 implies the square threshold here. "
                    + "This theorem leaves the classification of six-row unit relations, Hall conditions, "
                    + "complete-hull compositeness, higher-endpoint sectors, nonunit relations, "
                    + "larger cores, long spans and unrestricted Grimm's conjecture unresolved."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m"), h = F.Id("h"), a = F.Id("a"), b = F.Id("b");
        Formula c = F.Id("c"), d = F.Id("d"), e = F.Id("e"), f = F.Id("f");
        Formula upper = Add(m, h);
        Formula hypotheses = And(Lt(D(0), m), Le(D(0), h), Lt(new Formula.Power(h, D(2)), m),
            Le(m, a), Le(a, upper), Le(m, b), Le(b, upper), Le(m, c), Le(c, upper),
            Le(m, d), Le(d, upper), Le(m, e), Le(e, upper), Le(m, f), Le(f, upper),
            Eq(Mul(Mul(a, b), c), Mul(Mul(d, e), f)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("m"), Bound("h"), Bound("a"), Bound("b"), Bound("c"),
                Bound("d"), Bound("e"), Bound("f")],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies,
                Eq(Add(Add(a, b), c), Add(Add(d, e), f)))));
    }

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("Z"))));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(params Formula[] parts) => parts.Aggregate(
        (x, y) => new Formula.Logic(x, FormulaLogicOperator.And, y));
}
