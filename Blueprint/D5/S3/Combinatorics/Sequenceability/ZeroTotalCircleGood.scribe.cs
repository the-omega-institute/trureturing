using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class ZeroTotalCircleGoodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero total connects circular arcs to actual Good intervals",
        H("Zero total connects circular arcs to actual Good intervals"),
        Blocks(
            Describe.Lean(DescribeId.Create("rotated-two-runs"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/ZeroTotalCircleGood.rotated_two_runs"),
                H("One of two circular runs survives any rooting"),
                StatementSource.FromAuthor(RotatedStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This existing list lemma is exposed for direct reuse by PrivatePairBooleanDescent. "
                    + "For arbitrary lists u,v,w, if u followed by v is a rotation of w, then u or v "
                    + "is a contiguous interval of w. It needs no group structure or decidable equality; "
                    + "empty runs are allowed. The original proof is unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/ZeroTotalCircleGood.good_iff_no_zero_arc"),
                H("Zero total connects circular arcs to actual Good intervals"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "G ranges over additive commutative groups with decidable equality. Sum is coefficient-one "
                    + "original group addition. Good exempts exactly the full word, while Arc is an actual "
                    + "oriented circular run."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "Good means that every nonempty proper contiguous interval of an actual original-group "
                    + "word has nonzero sum; only the full word is exempt. At total sum zero, the complement of "
                    + "every proper zero arc is another proper zero arc.")),
            Paragraph(Text(
                    "For any rooting of a circle split into two nonempty runs, at least one whole run remains "
                    + "a linear interval. Consequently a zero circular arc makes every rooting bad. Conversely "
                    + "a bad proper interval supplies its actual finite label set and its circular arc. This "
                    + "proves the exact bridge without weakening the interval convention.")))));

    private static Formula RotatedStatement()
    {
        var g = FormulaDsl.Id("G"); var u = FormulaDsl.Id("u"); var v = FormulaDsl.Id("v");
        var w = FormulaDsl.Id("w"); var p = FormulaDsl.Id("p"); var q = FormulaDsl.Id("q");
        Formula Interval(Formula t) => new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("p"), C("List", g), new Formula.Bind(FormulaQuantifier.Exists,
                FormulaIdentifier.Create("q"), C("List", g), E(w, C("append", p, C("append", t, q)))));
        return Disp(A("G", C("Type"), A("u", C("List", g), A("v", C("List", g), A("w", C("List", g),
            Imp(C("IsRotated", C("append", u, v), w),
                new Formula.Logic(Interval(u), FormulaLogicOperator.Or, Interval(v))))))));
    }

    private static Formula Statement() =>
        Disp(
            A(
                "G",
                C("AddCommGroup"),
                A(
                    "A",
                    C("Finset", FormulaDsl.Id("G")),
                    A(
                        "w",
                        C("List", FormulaDsl.Id("G")),
                        Imp(
                            AndR(
                                E(C("sum", FormulaDsl.Id("A")), D(0)),
                                new Formula.Relation(
                                    FormulaDsl.Id("w"),
                                    FormulaRelationOperator.MemberOf,
                                    C("orders", FormulaDsl.Id("A"))
                                )
                            ),
                            IffR(
                                C("Good", FormulaDsl.Id("w")),
                                A(
                                    "S",
                                    C("Finset", FormulaDsl.Id("G")),
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
                                                    E(C("sum", FormulaDsl.Id("S")), D(0))
                                                )
                                            )
                                        ),
                                        new Formula.Not(
                                            C(
                                                "Arc",
                                                FormulaDsl.Id("A"),
                                                FormulaDsl.Id("S"),
                                                C("coeCycle", FormulaDsl.Id("w"))
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
    private static Formula IffR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Iff, Seq(Open, right, Close));
    private static Formula AndR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
}
