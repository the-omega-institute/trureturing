using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class CircularOrderCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Free rotation counts of original-label orders",
        H("Free rotation counts of original-label orders"),
        Blocks(
            Describe.Lean(DescribeId.Create("event-normalization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/CircularWords/CircularOrderCount.event_order_card"),
                H("Free rotation normalizes circular events"), StatementSource.FromAuthor(EventStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier has decidable equality. P is any predicate on Cycle(alpha). RootEvent(A,P) "
                    + "filters orders(A) by P of the actual rotation class; CircleEvent(A,P) filters circles(A) "
                    + "by P."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "An actual order of n distinct labels has n distinct rotations. The image in Mathlib "
                    + "Cycle retains orientation and identifies precisely those rotations. Every circle fiber "
                    + "therefore has exactly n rooted original-label words.")),
            Paragraph(Text(
                    "For any predicate on these circles, the number of rooted orders in that event is n times "
                    + "the number of event circles. The paired Good criterion is transported to such a circle "
                    + "predicate before this formula is used. A linear block event alone is not assumed "
                    + "rotation invariant.")),
            Paragraph(Text(
                    "ArcInventory(A,S) is the actual subset of circles(A) satisfying Arc A S, and sdiff(A,S) is "
                    + "A minus S. The carrier has decidable equality.")),
            Paragraph(Text(
                    "Orders(A) consists of the actual permutations of A.toList. Circles(A) is their image in "
                    + "the oriented List rotation quotient. A nonempty distinct-label word has exactly A.card "
                    + "distinct rotations, by the existing Mathlib rotation-freeness theorem.")),
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/CircularWords/CircularOrderCount.arc_filter_card"),
                H("Count a proper arc on the actual finite circle inventory"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every fiber of Orders(A) onto Circles(A) has size A.card. Counting the same finite fibers "
                    + "gives (A.card minus 1)! actual directed circles. The boundary contraction count then "
                    + "counts a single arc in this very same sample space. No independence assumption or quotient "
                    + "of original labels enters the argument."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "For a nonempty alphabet of distinct labels, event_order_card multiplies a circle-event "
                    + "count by A.card to recover its rooted-order count. PairedQuantitativeOrdering.quantitative_good_orders "
                    + "uses this equality to turn the Good-circle lower bound into a Good-order lower bound.")),
            Paragraph(Text(
                    "Only single-arc multiplicity and free rotation normalization are asserted here. "
                    + "Multiple-block intersections, complement-class event accounting, Bonferroni truncation and "
                    + "the residual tail are separate obligations before an all-rank Good-order bound can be "
                    + "concluded.")))));

    private static Formula EventStatement() =>
        Disp(
            A(
                "alpha",
                C("Type"),
                A(
                    "A",
                    C("Finset", FormulaDsl.Id("alpha")),
                    A(
                        "P",
                        C("PredicatesOn", C("Cycle", FormulaDsl.Id("alpha"))),
                        Imp(
                            C("Nonempty", FormulaDsl.Id("A")),
                            E(
                                C("card", C("RootEvent", FormulaDsl.Id("A"), FormulaDsl.Id("P"))),
                                Mul(
                                    C("card", FormulaDsl.Id("A")),
                                    C("card", C("CircleEvent", FormulaDsl.Id("A"), FormulaDsl.Id("P")))
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Statement() =>
        Disp(
            A(
                "alpha",
                C("Type"),
                A(
                    "A",
                    C("Finset", FormulaDsl.Id("alpha")),
                    A(
                        "S",
                        C("Finset", FormulaDsl.Id("alpha")),
                        Imp(
                            AndR(
                                new Formula.Relation(
                                    FormulaDsl.Id("S"),
                                    FormulaRelationOperator.SubsetOf,
                                    FormulaDsl.Id("A")
                                ),
                                AndR(
                                    C("Nonempty", FormulaDsl.Id("S")),
                                    C("Nonempty", C("sdiff", FormulaDsl.Id("A"), FormulaDsl.Id("S")))
                                )
                            ),
                            E(
                                C("card", C("ArcInventory", FormulaDsl.Id("A"), FormulaDsl.Id("S"))),
                                Mul(
                                    C("factorial", C("card", FormulaDsl.Id("S"))),
                                    C(
                                        "factorial",
                                        C("card", C("sdiff", FormulaDsl.Id("A"), FormulaDsl.Id("S")))
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
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula AndR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
