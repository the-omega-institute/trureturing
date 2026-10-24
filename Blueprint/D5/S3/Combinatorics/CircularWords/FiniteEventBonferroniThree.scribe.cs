using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class FiniteEventBonferroniThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Third finite Bonferroni bound on one event space",
        H("Third finite Bonferroni bound on one event space"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/CircularWords/FiniteEventBonferroniThree.bonferroni_three"),
                H("Third finite Bonferroni bound on one event space"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both carriers have decidable equality, with finite sets X and I. E assigns a predicate on "
                    + "alpha to each iota. Intersection(X,E,T) filters X by all events indexed by T; Avoid(X,E,I) "
                    + "filters by failure of every event indexed by I."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "For each point of one finite space, count the events that occur. The degree-p "
                    + "intersection memberships are exactly the p-element subsets of those events. The "
                    + "alternating binomial identity gives a nonpositive third odd truncation when any event "
                    + "occurs, and gives one when no event occurs.")),
            Paragraph(Text(
                    "Summing this pointwise inequality gives the third Bonferroni lower bound for the number "
                    + "avoiding every event. The actual paired circular intersections supply its moments. No "
                    + "joint law is replaced by a product of marginal counts.")))));

    private static Formula Statement() =>
        Disp(
            A(
                "alpha",
                C("Type"),
                A(
                    "iota",
                    C("Type"),
                    A(
                        "X",
                        C("Finset", FormulaDsl.Id("alpha")),
                        A(
                            "I",
                            C("Finset", FormulaDsl.Id("iota")),
                            A(
                                "E",
                                C("Predicates", FormulaDsl.Id("iota"), FormulaDsl.Id("alpha")),
                                Le(
                                    S(
                                        FormulaDsl.Id("p"),
                                        C("range", D(4)),
                                        Mul(
                                            new Formula.Power(Sub(D(0), D(1)), FormulaDsl.Id("p")),
                                            S(
                                                FormulaDsl.Id("T"),
                                                C(
                                                    "powersetCard",
                                                    FormulaDsl.Id("I"),
                                                    FormulaDsl.Id("p")
                                                ),
                                                C(
                                                    "card",
                                                    C(
                                                        "Intersection",
                                                        FormulaDsl.Id("X"),
                                                        FormulaDsl.Id("E"),
                                                        FormulaDsl.Id("T")
                                                    )
                                                )
                                            )
                                        )
                                    ),
                                    C(
                                        "card",
                                        C(
                                            "Avoid",
                                            FormulaDsl.Id("X"),
                                            FormulaDsl.Id("E"),
                                            FormulaDsl.Id("I")
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
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula S(Formula index, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(index, InMacro, domain)), Open, body, Close);
}
