using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class ActivityInnovationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWords/ActivityInnovations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successive centered bits of a positive activity path become orthogonal after "
        + "subtracting the linear prediction from the preceding bit, with explicit variances.",
        H("Orthogonal innovations of a binary exclusion path"),
        Blocks(
            Paragraph(Text(
                "There are n+2 sites, indexed from zero through n+1, with arbitrary n natural. "
                + "An activity vector w is strictly positive at every site. The probability "
                + "law w assigns the product of occupied-site activities to each legal Boolean "
                + "word, divides by the sum of these products, and assigns zero to words "
                + "with adjacent occupied sites. Write u=meansOf(w), so u(i) is the actual "
                + "occupied-state mean. These means are strictly interior.")),
            Paragraph(Text(
                "For bits a,b define edgeResidual(u,v,a,b)=(b-v)+v(a-u)/(1-u), interpreting "
                + "a and b as zero or one. The function innovation(u,b) has first coordinate "
                + "b(0)-u(0), and coordinate i+1 equal to edgeResidual(u(i),u(i+1),b(i),b(i+1)). "
                + "Thus it is R(i+1)-alpha(i) R(i), with R(i)=b(i)-u(i) and "
                + "alpha(i)=-u(i+1)/(1-u(i)). The seam is r(i)=1-u(i)-u(i+1).")),
            Describe.Lean(DescribeId.Create("orthogonal-innovations"),
                DeclarationHandle.Create(Prefix + "orthogonal_innovations"),
                H("Pairwise orthogonality and every squared norm"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The inner product is the finite probability sum of the product of "
                        + "two functions of the whole word. Any two distinct innovation "
                        + "coordinates are orthogonal. The first squared norm is u(0)(1-u(0)); "
                        + "the squared norm at i+1 is u(i+1)r(i)/(1-u(i)), for every edge. "
                        + "The indexing includes the two-site path when n=0.")),
                    Paragraph(Text(
                        "The activity law is the first-order completion of its means. "
                        + "Group a finite expectation by its exact initial histories. The "
                        + "Markov cylinder recursion expresses one further bit using a "
                        + "two-state transition row. Exclusion and the positive occupied "
                        + "marginal force the true-to-true entry to vanish. The next-site "
                        + "mean forces the false-to-true entry to be u(i+1)/(1-u(i)). "
                        + "Summing edgeResidual against either row gives zero. Consequently "
                        + "each new residual is orthogonal to every function of its past, "
                        + "including each earlier innovation.")),
                    Paragraph(Text(
                        "A centered Boolean variable of mean u has second moment u(1-u). "
                        + "Write a=u(i+1)/(1-u(i)) and E=R(i+1)+a R(i). The identity "
                        + "E squared = R(i+1) squared - a squared R(i) squared + 2a R(i)E, "
                        + "together with orthogonality to R(i), reduces the new variance "
                        + "to the two one-site variances. Simplifying gives the displayed "
                        + "positive expression."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Sum(Formula count, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id("b"), Colon, Sp,
            new Formula.TypeArrow(Call("Fin", count), Call("Bool")))), Sp, Grp(body));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), i = F.Id("i"), j = F.Id("j"), b = F.Id("b");
        Formula count = Add(n, D(2)), u = Call("meansOf", w);
        Formula Mean(Formula k) => new Formula.Apply(u, [k]);
        Formula E(Formula k) => Call("innovation", u, b, k);
        Formula Norm(Formula k) => Sum(count, Mul(Call("law", w, b), new Formula.Superscript(E(k), D(2))));
        Formula orth = All("i", Call("Fin", count), All("j", Call("Fin", count),
            Imp(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j),
                Eq(Sum(count, Mul(Mul(Call("law", w, b), E(i)), E(j))), D(0)))));
        Formula first = Eq(Norm(D(0)), Mul(Mean(D(0)), Sub(D(1), Mean(D(0)))));
        Formula edge = All("i", Call("Fin", Add(n, D(1))),
            Eq(Norm(Call("succ", i)), new Formula.Fraction(
                Mul(Mean(Add(Call("val", i), D(1))), Call("seam", u, Call("val", i))),
                Sub(D(1), Mean(Call("val", i))))));
        Formula positive = All("i", Call("Fin", count),
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, new Formula.Apply(w, [i])));
        return Disp(All("n", Nat(), All("w", new Formula.TypeArrow(Call("Fin", count), Real()),
            Imp(positive, And(orth, And(first, edge))))));
    }
}
