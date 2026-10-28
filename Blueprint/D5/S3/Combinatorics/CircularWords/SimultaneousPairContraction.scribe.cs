using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class SimultaneousPairContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous opposite-pair block intersections",
        H("Simultaneous opposite-pair block intersections"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/CircularWords/SimultaneousPairContraction.joint_pair_card"),
                H("Simultaneous opposite-pair block intersections"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier has decidable equality. DisjointPairFamily(A,F) means that every member of F "
                    + "is a two-element subset of A and distinct members are disjoint. JointInventory(A,F) "
                    + "consists of actual cycles satisfying Joint A F."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "A joint event consists of actual oriented circles realizing every prescribed disjoint "
                    + "run. The jointStepEquiv contracts one run while preserving every remaining event on that "
                    + "same circle. Its two inverse maps use the recorded original internal order and actual "
                    + "marker expansion.")),
            Paragraph(Text(
                    "Iterating this equivalence for p disjoint two-label blocks gives 2^p times (n-p-1)! "
                    + "circles when 2p<n. The paired quantitative consumer uses p=0,1,2,3 with n=2r and r at "
                    + "least twelve. Distinct original labels and the free rotation fibers supply the "
                    + "normalization; event independence is neither assumed nor asserted.")))));

    private static Formula Statement() =>
        Disp(
            A(
                "alpha",
                C("Type"),
                A(
                    "A",
                    C("Finset", FormulaDsl.Id("alpha")),
                    A(
                        "F",
                        C("Finset", C("Finset", FormulaDsl.Id("alpha"))),
                        Imp(
                            AndR(
                                C("DisjointPairFamily", FormulaDsl.Id("A"), FormulaDsl.Id("F")),
                                LtR(
                                    Mul(D(2), C("card", FormulaDsl.Id("F"))),
                                    C("card", FormulaDsl.Id("A"))
                                )
                            ),
                            E(
                                C("card", C("JointInventory", FormulaDsl.Id("A"), FormulaDsl.Id("F"))),
                                Mul(
                                    new Formula.Power(D(2), C("card", FormulaDsl.Id("F"))),
                                    C(
                                        "factorial",
                                        Sub(
                                            Sub(
                                                C("card", FormulaDsl.Id("A")),
                                                C("card", FormulaDsl.Id("F"))
                                            ),
                                            D(1)
                                        )
                                    )
                                )
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
    private static Formula E(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LtR(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula AndR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
