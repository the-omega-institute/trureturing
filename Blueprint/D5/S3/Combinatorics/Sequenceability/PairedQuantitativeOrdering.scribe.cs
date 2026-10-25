using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class PairedQuantitativeOrderingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite uniform quantitative bound for paired C3 Good orders",
        H("A finite uniform quantitative bound for paired C3 Good orders"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PairedQuantitativeOrdering.quantitative_good_orders"),
                H("A finite uniform quantitative bound for paired C3 Good orders"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "GoodOrders(r) is the actual finite set of original signed coordinate-label orders "
                    + "satisfying Good. LowerFraction(r) is exactly the explicit rational polynomial fraction "
                    + "defined below; no count or numerical premise is assumed."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "For every natural r at least twelve, take the original distinct labels plus and minus "
                    + "the r coordinate basis vectors in C3^r. The theorem counts actual permutations of this "
                    + "alphabet with coefficient one and original group addition. Every nonempty proper "
                    + "contiguous interval must have nonzero sum; the full word alone is exempt.")),
            Paragraph(Text(
                    "The lower bound is (2r)! times (8r^3-123r^2+388r-45)/(3(2r-1)(2r-3)(2r-5)), and the "
                    + "fraction is strictly positive. The proof combines actual simultaneous circular block "
                    + "contractions, the third finite Bonferroni estimate, exact complement pairing, and the "
                    + "finite symmetric binomial tail. At r=12+s the numerator is 8s^3+165s^2+892s+723. The "
                    + "zero-total seam bridge and free rotation fibers identify the result with the actual "
                    + "rooted Good orders.")),
            Paragraph(Text(
                    "This improves understanding of event overlap where the first-moment estimate fails. The "
                    + "corresponding words are known as rooted connected chord diagrams after forgetting "
                    + "coordinate names and signs. Mahmoud and Yeats, Connected Chord Diagrams and the "
                    + "Combinatorics of Asymptotic Expansions, arXiv:2010.06550v2, give a stronger asymptotic "
                    + "expansion for that established class. No novelty or priority for this finite certificate "
                    + "is claimed. This result concerns this paired alphabet only; unrestricted AM and "
                    + "arbitrary-subset sequenceability are not resolved.")))));

    private static Formula Statement() =>
        Disp(
            A(
                "r",
                C("Nat"),
                Imp(
                    Le(D(1, 2), FormulaDsl.Id("r")),
                    AndR(
                        Le(
                            Mul(
                                C("factorial", Mul(D(2), FormulaDsl.Id("r"))),
                                C("lowerFraction", FormulaDsl.Id("r"))
                            ),
                            C("card", C("goodOrders", FormulaDsl.Id("r")))
                        ),
                        AndR(
                            LtR(D(0), C("lowerFraction", FormulaDsl.Id("r"))),
                            LtR(D(0), C("card", C("goodOrders", FormulaDsl.Id("r"))))
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
    private static Formula LtR(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula AndR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
