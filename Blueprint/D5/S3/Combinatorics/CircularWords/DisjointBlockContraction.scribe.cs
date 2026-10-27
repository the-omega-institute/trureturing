using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class DisjointBlockContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-label circular run contraction",
        H("Original-label circular run contraction"),
        Blocks(
            Paragraph(Text(
                    "The carrier has decidable equality. The primed lists are separate original internal "
                    + "orders; coeCycle identifies rotation only, and Perm compares with the displayed finite set "
                    + "list.")),
            Paragraph(Text(
                    "Let A be a finite set of distinct original labels and S a nonempty proper subset. An arc "
                    + "is an oriented circle represented by an ordering of S followed by an ordering of its "
                    + "complement. Rotation preserves orientation; reversal is not identified.")),
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/CircularWords/DisjointBlockContraction.two_block_injective"),
                H("A proper circular run has a unique incoming boundary"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two such representatives of the same circle are equal. The first label of each lies in S "
                    + "and the last lies outside S. A nonzero rotation starting in the complement has the wrong "
                    + "first label; one starting strictly inside the S run has the wrong last label. Hence the "
                    + "incoming boundary fixes the representative. The resulting twoBlockEquiv gives mutually "
                    + "inverse actual two-block expansion and boundary cutting, and arc_card counts S.card! times "
                    + "(A minus S).card! circles."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "Expansion also replaces every marker in one common marker circle by its full "
                    + "original-label run. Restricting expanded labels commutes with expansion; the retained "
                    + "original marker and the recorded internal order give the contraction interface. The "
                    + "simultaneous pair intersection formula and the quantitative Good-order estimate use this "
                    + "expansion on the same oriented circle.")))));

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
                            "u",
                            C("List", FormulaDsl.Id("alpha")),
                            A(
                                "v",
                                C("List", FormulaDsl.Id("alpha")),
                                A(
                                    "uprime",
                                    C("List", FormulaDsl.Id("alpha")),
                                    A(
                                        "vprime",
                                        C("List", FormulaDsl.Id("alpha")),
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
                                                            C(
                                                                "sdiff",
                                                                FormulaDsl.Id("A"),
                                                                FormulaDsl.Id("S")
                                                            )
                                                        ),
                                                        AndR(
                                                            C(
                                                                "Perm",
                                                                FormulaDsl.Id("u"),
                                                                C("toList", FormulaDsl.Id("S"))
                                                            ),
                                                            AndR(
                                                                C(
                                                                    "Perm",
                                                                    FormulaDsl.Id("v"),
                                                                    C(
                                                                        "toList",
                                                                        C(
                                                                            "sdiff",
                                                                            FormulaDsl.Id("A"),
                                                                            FormulaDsl.Id("S")
                                                                        )
                                                                    )
                                                                ),
                                                                AndR(
                                                                    C(
                                                                        "Perm",
                                                                        FormulaDsl.Id("uprime"),
                                                                        C("toList", FormulaDsl.Id("S"))
                                                                    ),
                                                                    AndR(
                                                                        C(
                                                                            "Perm",
                                                                            FormulaDsl.Id("vprime"),
                                                                            C(
                                                                                "toList",
                                                                                C(
                                                                                    "sdiff",
                                                                                    FormulaDsl.Id("A"),
                                                                                    FormulaDsl.Id("S")
                                                                                )
                                                                            )
                                                                        ),
                                                                        E(
                                                                            C(
                                                                                "coeCycle",
                                                                                C(
                                                                                    "append",
                                                                                    FormulaDsl.Id("u"),
                                                                                    FormulaDsl.Id("v")
                                                                                )
                                                                            ),
                                                                            C(
                                                                                "coeCycle",
                                                                                C(
                                                                                    "append",
                                                                                    FormulaDsl.Id(
                                                                                        "uprime"
                                                                                    ),
                                                                                    FormulaDsl.Id(
                                                                                        "vprime"
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            ),
                                            AndR(
                                                E(FormulaDsl.Id("u"), FormulaDsl.Id("uprime")),
                                                E(FormulaDsl.Id("v"), FormulaDsl.Id("vprime"))
                                            )
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
