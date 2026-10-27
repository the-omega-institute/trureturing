using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class PairedNoAdjacencyEstimateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit density of circles without opposite-pair adjacencies",
        H("Explicit density of circles without opposite-pair adjacencies"),
        Blocks(
            Describe.Lean(DescribeId.Create("general-bonferroni"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate.bonferroni_three"),
                H("Third finite Bonferroni bound on one event space"), StatementSource.FromAuthor(BonferroniStatement()), AssessedProvenance.FromRepo(),
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
                    + "joint law is replaced by a product of marginal counts.")),
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate.no_adjacency_lower_bound"),
                H("Explicit density of circles without opposite-pair adjacencies"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "NoAdjacency(r) is the actual subset of circles(alphabet(r)) in which no designated "
                    + "opposite pair is adjacent. Every count and factorial in the displayed ratios is "
                    + "interpreted in the rationals."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "pointwise_three bounds the alternating binomial sum for the number of events occurring "
                    + "at each point. intersection_moment counts those binomial coefficients by actual event "
                    + "intersections. Summing yields bonferroni_three; simultaneous-pair contraction counts then "
                    + "give no_adjacency_lower_bound on the same circle inventory.")),
            Paragraph(Text(
                    "The actual degree-zero through degree-three intersection counts give the third odd "
                    + "Bonferroni truncation on the original paired circle inventory. Dividing by its positive "
                    + "cardinality (2r-1)! gives the density lower bound (4r^2-11r+9)/(3(2r-1)(2r-3)).")),
            Paragraph(Text(
                    "These are simultaneous contractions of distinct original pairs on one oriented circle. "
                    + "In particular the pairwise intersection count is not the product of its marginal counts. "
                    + "This estimate is consumed together with the unconditional residual zero-block bound.")))));

    private static Formula BonferroniStatement() =>
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

    private static Formula Statement() =>
        Disp(
            A(
                "r",
                C("Nat"),
                Imp(
                    Le(D(1, 2), FormulaDsl.Id("r")),
                    Le(
                        new Formula.Fraction(
                            AddR(
                                Sub(
                                    Mul(D(4), new Formula.Power(FormulaDsl.Id("r"), D(2))),
                                    Mul(D(1, 1), FormulaDsl.Id("r"))
                                ),
                                D(9)
                            ),
                            Mul(
                                Mul(D(3), Sub(Mul(D(2), FormulaDsl.Id("r")), D(1))),
                                Sub(Mul(D(2), FormulaDsl.Id("r")), D(3))
                            )
                        ),
                        new Formula.Fraction(
                            C("card", C("noAdjacency", FormulaDsl.Id("r"))),
                            C("factorial", Sub(Mul(D(2), FormulaDsl.Id("r")), D(1)))
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
    private static Formula AddR(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula S(Formula index, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(index, InMacro, domain)), Open, body, Close);
}
