using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class CircleBlockEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual circular run contraction",
        H("Actual circular run contraction"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/CircularWords/CircleBlockEquivalence.blockEquiv_expand"),
                H("Actual circular run contraction"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier has decidable equality. BlockDomain(A,S,a) is the product of orders(S) and "
                    + "circles(insert(a,sdiff(A,S))). First and second are its actual ordered-run and circle "
                    + "components. Proof arguments of blockEquiv are suppressed in this presentation."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "Keep one original label of a nonempty proper run as its marker. Cutting at the unique "
                    + "incoming boundary records its internal order and the complementary order. Anchoring the "
                    + "contracted circle at the marker gives the inverse map. Expansion replaces that marker by "
                    + "the entire recorded run in its original orientation.")),
            Paragraph(Text(
                    "Restriction deletes the other labels of this run. It recovers the contracted circle, and "
                    + "expansion preserves and reflects every prescribed arc disjoint from the contracted run. "
                    + "This is the common-circle interface used by the simultaneous contraction, rather than "
                    + "separate cuts chosen for different events.")))));

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
                        A(
                            "a",
                            FormulaDsl.Id("alpha"),
                            A(
                                "z",
                                C(
                                    "BlockDomain",
                                    FormulaDsl.Id("A"),
                                    FormulaDsl.Id("S"),
                                    FormulaDsl.Id("a")
                                ),
                                Imp(
                                    AndR(
                                        new Formula.Relation(
                                            FormulaDsl.Id("S"),
                                            FormulaRelationOperator.SubsetOf,
                                            FormulaDsl.Id("A")
                                        ),
                                        AndR(
                                            C("Nonempty", FormulaDsl.Id("S")),
                                            AndR(
                                                C(
                                                    "Nonempty",
                                                    C("sdiff", FormulaDsl.Id("A"), FormulaDsl.Id("S"))
                                                ),
                                                new Formula.Relation(
                                                    FormulaDsl.Id("a"),
                                                    FormulaRelationOperator.MemberOf,
                                                    FormulaDsl.Id("S")
                                                )
                                            )
                                        )
                                    ),
                                    E(
                                        C(
                                            "value",
                                            C(
                                                "blockEquiv",
                                                FormulaDsl.Id("A"),
                                                FormulaDsl.Id("S"),
                                                FormulaDsl.Id("a"),
                                                FormulaDsl.Id("z")
                                            )
                                        ),
                                        C(
                                            "inflate",
                                            FormulaDsl.Id("a"),
                                            C("first", FormulaDsl.Id("z")),
                                            C("value", C("second", FormulaDsl.Id("z")))
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
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula AndR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
}
