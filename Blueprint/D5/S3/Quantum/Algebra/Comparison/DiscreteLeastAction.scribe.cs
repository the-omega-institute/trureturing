using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Comparison;

internal sealed class DiscreteLeastActionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/Comparison/DiscreteLeastAction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least cosine action for nonnegative steps of fixed total at most pi.",
        H("Discrete least action on a finite simplex"),
        Blocks(Describe.Lean(DescribeId.Create("discrete-cosine-least-action"),
            DeclarationHandle.Create(Module + ".sum_one_sub_cos_least_action"),
            H("Equal angles minimize the action"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The manuscript Ternions and minimal arcs states the "
                    + "strict total-angle case as F5 for a positive number of steps. The action "
                    + "adds one minus the cosine of each step. On an empty family the total is zero "
                    + "and Lean's real quotient by zero is zero. The cardinality factor vanishes, "
                    + "both actions are zero, and the equality condition is vacuous.")),
                Paragraph(Text("Cosine is strictly concave between zero and pi over two, where "
                    + "finite Jensen's inequality gives the bound and its equality condition. "
                    + "A single step already equals the total. If a larger family has a step above "
                    + "pi over two, averaging it with any other step preserves "
                    + "the total and brings all steps into that interval. The cosine sum cannot "
                    + "decrease under this averaging, and it increases strictly if the two steps "
                    + "differ and their sum is less than pi. Equality for a pair containing a large "
                    + "step therefore requires that the pair already sum to pi. Jensen equality "
                    + "would then force every remaining step to be pi over two, so the pair must "
                    + "exhaust the index type. At total pi the two cosines cancel for every split.")),
                Paragraph(Text("For two unequal, nonnegative steps whose total is just above pi, "
                    + "the cosine of their mean is negative. The two-angle cosine formula then gives "
                    + "a smaller action than that of the equal split. Allowing negative steps also "
                    + "invalidates the bound. With steps zero and minus twice pi, the action is zero "
                    + "and the uniform action is four. The sum premise ties the proposed total to "
                    + "the actual steps. With a single zero step but prescribed total pi over two, "
                    + "the proposed lower bound would be one while the action is zero. These examples "
                    + "follow from the two-angle formula and direct substitution and were checked by hand."))),
            DescribeRole.Theorem))));

    private static Formula All(string name, Formula type, Formula value) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, value);
    private static Formula At(Formula index) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("t"), [index]);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Instance(string name) =>
        Seq(OpenBracket, F.Id(name), Sp, Iota, CloseBracket, Sp);
    private static Formula SumOver(Formula term) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id("i"), Sp, InMacro, Sp, Iota)), Sp, term);
    private static Formula Loss(Formula angle) =>
        new Formula.Binary(D(1), FormulaBinaryOperator.Subtract,
            Seq(Operatorname, Grp(F.Id("cos")), Open, angle, Close));

    private static Formula Statement()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula i = F.Id("i");
        Formula card = new Formula.Absolute(Iota);
        Formula mean = new Formula.Fraction(Theta, card);
        Formula action = SumOver(Seq(Open, Loss(At(i)), Close));
        Formula uniform = new Formula.Binary(card, FormulaBinaryOperator.Multiply,
            Seq(Open, Loss(mean), Close));
        Formula equalityCases = new Formula.Logic(All("i", Iota, Eq(At(i), mean)),
            FormulaLogicOperator.Or, And(Eq(card, D(2)), Eq(Theta, Pi)));
        Formula conclusion = And(Le(uniform, action),
            new Formula.Logic(Eq(action, uniform), FormulaLogicOperator.Iff, equalityCases));
        Formula hypotheses = And(All("i", Iota, Le(D(0), At(i))),
            And(Eq(SumOver(At(i)), Theta), Le(Theta, Pi)));
        return Disp(Seq(Forall, Sp, Iota, Sp, Colon, Sp, F.Id("Type"), Comma, Sp,
            Instance("Fintype"),
            All("t", Seq(Iota, Sp, To, Sp, real),
                Seq(Forall, Sp, Theta, Sp, Colon, Sp, real, Comma, Sp,
                    new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)))));
    }
}
