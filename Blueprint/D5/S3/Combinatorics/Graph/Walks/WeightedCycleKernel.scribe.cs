using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class WeightedCycleKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic Transport and Weighted Rank",
        H("Cyclic Transport and Weighted Rank"), Blocks(
            Paragraph(Text("Let K be any field and n any natural number. The coordinates are indexed by Fin(n+1). Write sigma=finRotate(n+1), P(k)=product of r(j) for j<k, and T_r(x)(i)=x(sigma(i))-r(i)x(i). Zero coefficients are permitted in r. The argument works for every length, including one coordinate. The cyclic bipartite conclusion additionally assumes characteristic two and nonzero b(i).")),
            Describe.Lean(DescribeId.Create("transport-nullity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedCycleKernel.transport_nullity"),
                H("Cyclic transport nullity"), StatementSource.FromAuthor(TransportNullityFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every r:Fin(n+1)->K, the kernel dimension of T_r is one if product(r)=1 and zero otherwise. Kernel coordinates satisfy x(k)=P(k)x(0). Evaluation at zero is injective. The last equation gives x(0)=product(r)x(0); if the product is not one, all coordinates vanish. If it is one, the prefix-product vector is a nonzero kernel vector. This is the all-length inference used in the weighted rank calculation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-bipartite-rank"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedCycleKernel.cyclic_bipartite_rank"),
                H("Rank of the cyclic bipartite block"), StatementSource.FromAuthor(CyclicBipartiteRankFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Let B(i,j)=[j=i]a(i)+[j=sigma(i)]b(i), with every b(i) nonzero. The symmetric block matrix [0 B; transpose(B) 0] has rank 2n if product(a)=product(b), and 2(n+1) otherwise. In characteristic two its kernel equation becomes cyclic transport with r(i)=a(i)/b(i). Rank-nullity computes rank(B). The two off-diagonal kernel components give twice that rank. The coefficients a(i) are unrestricted."))),
                DescribeRole.Theorem))));

    private static Formula TransportNullityFormula()
    {
        Formula k = F.Id("K"), n = F.Id("n"), r = F.Id("r");
        Formula domain = Arrow(Fin(Add(n, D(1))), k);
        Formula conclusion = Eq(Call("finrank", k, Call("ker", Call("transport", r))),
            Call("If", Eq(Call("product", r), D(1)), D(1), D(0)));
        return Disp(All("K", F.Id("Type"),
            Seq(Instance("Field", k), All("n", Nat(), All("r", domain, conclusion)))));
    }

    private static Formula CyclicBipartiteRankFormula()
    {
        Formula k = F.Id("K"), n = F.Id("n"), a = F.Id("a"), b = F.Id("b");
        Formula family = Fin(Add(n, D(1)));
        Formula matrix = Call("cyclicBidiagonal", a, b);
        Formula block = Call("fromBlocks", D(0), matrix, Call("transpose", matrix), D(0));
        Formula hypothesis = ForAll("i", family, NotEqual(Call("b", F.Id("i")), D(0)));
        Formula conclusion = Eq(Call("rank", block),
            Call("If", Eq(Call("product", a), Call("product", b)),
                Mul(D(2), n), Mul(D(2), Add(n, D(1)))));
        return Disp(All("K", F.Id("Type"),
            Seq(Instance("Field", k), All("n", Nat(),
                Seq(InstanceAt("CharP", k, D(2)),
                    All("a", Arrow(family, k),
                        All("b", Arrow(family, k), Implies(hypothesis, conclusion))))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula ForAll(string name, Formula type, Formula body) => All(name, type, body);

    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);

    private static Formula InstanceAt(string name, Formula type, Formula value) =>
        Seq(OpenBracket, Call(name, type, value), CloseBracket, Sp);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Nat() => Call("Nat");
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, b);
    private static Formula Call(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. a]);
}
