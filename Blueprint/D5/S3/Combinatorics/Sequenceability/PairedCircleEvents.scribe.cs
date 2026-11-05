using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class PairedCircleEventsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original C3 pair events on one circle inventory",
        H("Original C3 pair events on one circle inventory"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PairedCircleEvents.adjacency_intersection_card"),
                H("Original C3 pair events on one circle inventory"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "AdjacencyIntersection(r,T) is the subset of circles(alphabet(r)) realizing adjacency i for "
                    + "every i in T. This count uses one common oriented circle space."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "The original alphabet in Fin r to ZMod 3 consists of the distinct signed coordinate "
                    + "vectors. A coordinate subset I gives its actual union of opposite pairs, of cardinality "
                    + "2 times card(I). Complementation of coordinate subsets corresponds exactly to "
                    + "complementation in the original alphabet.")),
            Paragraph(Text(
                    "For any prescribed coordinate subset T of size at most three and r at least twelve, the "
                    + "common-circle contraction yields exactly 2^card(T) times (2r-card(T)-1)! simultaneous "
                    + "adjacency circles. Enumerating the coordinate subsets gives the binomial moments "
                    + "consumed by the third Bonferroni estimate.")))));

    private static Formula Statement() =>
        Disp(
            A(
                "r",
                C("Nat"),
                A(
                    "T",
                    C("Finset", C("Fin", FormulaDsl.Id("r"))),
                    Imp(
                        AndR(Le(D(1, 2), FormulaDsl.Id("r")), Le(C("card", FormulaDsl.Id("T")), D(3))),
                        E(
                            C(
                                "card",
                                C("AdjacencyIntersection", FormulaDsl.Id("r"), FormulaDsl.Id("T"))
                            ),
                            Mul(
                                new Formula.Power(D(2), C("card", FormulaDsl.Id("T"))),
                                C(
                                    "factorial",
                                    Sub(
                                        Sub(
                                            Mul(D(2), FormulaDsl.Id("r")),
                                            C("card", FormulaDsl.Id("T"))
                                        ),
                                        D(1)
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
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula AndR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
