using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class CircleEventNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Free rotation normalizes circular events",
        H("Free rotation normalizes circular events"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/CircularWords/CircleEventNormalization.event_order_card"),
                H("Free rotation normalizes circular events"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
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
                    + "rotation invariant.")))));

    private static Formula Statement() =>
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

    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula E(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
