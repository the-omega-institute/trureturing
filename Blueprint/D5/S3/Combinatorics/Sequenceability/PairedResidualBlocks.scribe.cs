using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class PairedResidualBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complement pairing of residual zero blocks",
        H("Complement pairing of residual zero blocks"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PairedResidualBlocks.residual_mass_le"),
                H("Complement pairing of residual zero blocks"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Bad(r) is the union of all remaining forbidden original-label block events with pair-index "
                    + "sizes from two through r minus two. Counts and factorials are coerced to the rationals in "
                    + "this inequality."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "After removing single-pair adjacency events and their complements, the remaining "
                    + "coordinate subsets have cardinalities from two through r-2. Complementation preserves "
                    + "this range and the actual circular event. It has no fixed coordinate subset when r is "
                    + "positive, including at the middle cardinality.")),
            Paragraph(Text(
                    "Every occurrence therefore supplies two distinct complementary subset witnesses in the "
                    + "same actual circle. Summing these memberships bounds twice the residual bad-circle count "
                    + "by the full subset-event sum. Exact single-arc contraction and grouping by cardinality "
                    + "turn half of that sum into r times the finite binomial tail. The mass is unconditional; "
                    + "no independence from adjacency avoidance is used.")))));

    private static Formula Statement() =>
        Disp(
            A(
                "r",
                C("Nat"),
                Imp(
                    Le(D(6), FormulaDsl.Id("r")),
                    Le(
                        new Formula.Fraction(
                            C("card", C("bad", FormulaDsl.Id("r"))),
                            C("factorial", Sub(Mul(D(2), FormulaDsl.Id("r")), D(1)))
                        ),
                        Mul(
                            FormulaDsl.Id("r"),
                            S(
                                FormulaDsl.Id("j"),
                                C("Icc", D(2), Sub(FormulaDsl.Id("r"), D(2))),
                                C("density", FormulaDsl.Id("r"), FormulaDsl.Id("j"))
                            )
                        )
                    )
                )
            )
        );

    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula S(Formula index, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(index, InMacro, domain)), Open, body, Close);
}
