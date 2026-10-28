using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class PairedBinomialTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform finite paired binomial tail",
        H("Uniform finite paired binomial tail"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PairedBinomialTail.paired_tail_bound"),
                H("Uniform finite paired binomial tail"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum runs over every integer j from two through r minus two. Density(r,j) is "
                    + "choose(r,j) divided by choose(2r,2j), in the rationals."))), DescribeRole.Theorem),
            Paragraph(Text(
                    "Let f(r,j) be binomial(r,j) divided by binomial(2r,2j), with rational division. The "
                    + "exact adjacent-index ratio is (2j+1)/(2r-2j-1), and complementation gives "
                    + "f(r,r-j)=f(r,j). Hence the sequence decreases toward the middle.")),
            Paragraph(Text(
                    "For r at least six, the tail from j=2 through r-2 has two endpoint terms f(r,2) and "
                    + "exactly r-5 middle terms bounded by f(r,3). The endpoint values are 3/((2r-1)(2r-3)) and "
                    + "15/((2r-1)(2r-3)(2r-5)). This yields the explicit residual mass "
                    + "r(27r-105)/((2r-1)(2r-3)(2r-5)), uniformly in r.")))));

    private static Formula Statement() =>
        Disp(
            A(
                "r",
                C("Nat"),
                Imp(
                    Le(D(6), FormulaDsl.Id("r")),
                    Le(
                        Mul(
                            FormulaDsl.Id("r"),
                            S(
                                FormulaDsl.Id("j"),
                                C("Icc", D(2), Sub(FormulaDsl.Id("r"), D(2))),
                                C("density", FormulaDsl.Id("r"), FormulaDsl.Id("j"))
                            )
                        ),
                        new Formula.Fraction(
                            Mul(FormulaDsl.Id("r"), Sub(Mul(D(2, 7), FormulaDsl.Id("r")), D(1, 0, 5))),
                            Mul(
                                Mul(
                                    Sub(Mul(D(2), FormulaDsl.Id("r")), D(1)),
                                    Sub(Mul(D(2), FormulaDsl.Id("r")), D(3))
                                ),
                                Sub(Mul(D(2), FormulaDsl.Id("r")), D(5))
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
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula S(Formula index, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(index, InMacro, domain)), Open, body, Close);
}
