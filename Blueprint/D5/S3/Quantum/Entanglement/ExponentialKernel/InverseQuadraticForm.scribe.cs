using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.ExponentialKernel;

internal sealed class InverseQuadraticFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly ordered finite real sites give a nonsingular exponential matrix with an exact innovation quadratic form.",
        H("Inverse Quadratic Form of an Ordered Exponential Kernel"),
        Blocks(
            Paragraph(Text(
                "For n+1 real sites loss(0),...,loss(n), let K(n,loss) be the real matrix "
                + "indexed by Fin(n+1) with entry kernel(loss,i,j)=exp(-abs(loss(i)-loss(j))/2). "
                + "Write edge(loss,i)=exp(-(loss(i+1)-loss(i))/2). Only the adjacent inequalities "
                + "within this finite prefix are assumed. Values of loss beyond n are unrestricted.")),
            Describe.Lean(
                DescribeId.Create("inverse-quadratic-form"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/ExponentialKernel/InverseQuadraticForm.inverse_quadratic_form"),
                H("Nonsingularity and the complete quadratic identity"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The inverse in the formula is the nonsingular matrix inverse. "
                        + "For i in Fin(n), castSucc(i) denotes the index i in Fin(n+1), "
                        + "and succ(i) denotes its next index i+1. The first coordinate is indexed by zero.")),
                    Paragraph(Text(
                        "The innovation matrix A sends x to the vector with initial coordinate x(0) "
                        + "and subsequent coordinates x(i+1)-edge(loss,i)x(i). The exponential addition "
                        + "law and the order of the sites give A K A transpose equal to the diagonal "
                        + "matrix with initial entry one and subsequent entries one minus the square "
                        + "of edge(loss,i). Each edge lies strictly "
                        + "between zero and one, so this diagonal matrix is invertible. Matrix inverse "
                        + "uniqueness then identifies K inverse with A transpose times the inverse "
                        + "diagonal matrix times A. Expanding its quadratic form gives every displayed term.")),
                    Paragraph(Text(
                        "When n=0 the matrix has the single entry one, the adjacent-order "
                        + "hypothesis is empty, and the sum over Fin(0) is empty. The identity is x(0) squared. "
                        + "The construction is the usual unequal-gap AR(1), or sampled Ornstein-Uhlenbeck, "
                        + "innovation factorization. It concerns the real exponential matrix; a physical "
                        + "channel optimum requires its separate channel and norm arguments."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Subtract(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Statement()
    {
        Formula n = F.Id("n"), loss = F.Id("loss"), i = F.Id("i"), x = F.Id("x");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula k = Call("K", n, loss);
        Formula inverse = Pow(k, Seq(Minus, D(1)));
        Formula order = All("i", naturals, Arrow(
            new Formula.Relation(i, FormulaRelationOperator.LessThan, n),
            new Formula.Relation(Call("loss", i), FormulaRelationOperator.LessThan,
                Call("loss", Add(i, D(1))))));
        Formula nonsingular = Seq(Call("det", k), Sp, Neq, Sp, D(0));
        Formula inverseLaw = Eq(Seq(k, Sp, inverse), D(1));
        Formula edge = Call("edge", loss, i);
        Formula residual = Subtract(Call("x", Call("succ", i)),
            Seq(edge, Sp, Call("x", Call("castSucc", i))));
        Formula summand = Seq(Frac, Grp(Pow(residual, D(2))),
            Grp(Subtract(D(1), Pow(edge, D(2)))));
        Formula sum = Seq(Sum, Underscore,
            Grp(i, Sp, InMacro, Sp, Call("Fin", n)), Sp, summand);
        Formula form = Eq(Seq(Pow(x, F.Id("T")), Sp, inverse, Sp, x),
            Add(Pow(Call("x", D(0)), D(2)), sum));
        Formula vectors = Seq(Call("Fin", Add(n, D(1))), Sp, To, Sp, reals);
        return Disp(All("n", naturals, All("loss", Seq(naturals, Sp, To, Sp, reals),
            Arrow(order, And(nonsingular, And(inverseLaw, All("x", vectors, form)))))));
    }
}
