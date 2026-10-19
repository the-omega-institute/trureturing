using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntryProductMixtureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/SingleEntryProductMixture.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict lattice minors for an ordered mixture of actual Bernoulli site occupancies.",
        H("A common mixing variable creates strict positive dependence"),
        Blocks(
            Node("productKernel", "Conditional product mass",
                "For a finite site set I and an occupied subset S, the kernel is the product of g(i,u) on S and 1-g(i,u) off S. Thus each fixed u gives the ordinary product Bernoulli law.", DescribeRole.Definition),
            Node("mixtureMass", "Shared-variable integral mass",
                "The mass of S is the integral from zero to t of h(u) times its product kernel. All configurations share the same mixing weight h and the same site functions. A common positive normalization does not change the sign of a lattice minor.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-entry-strict-product-mixture"),
                DeclarationHandle.Create(Prefix + "strict_mtp2_product_mixture"),
                H("Every incomparable minor is strict"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume t>0, continuous nonnegative h on [0,t], and strictly positive h in its interior. Each site occupancy is continuous, lies in [0,1), and is strictly increasing. For incomparable S and T, both differences S\\T and T\\S are nonempty. Write the site odds as g/(1-g). Absorb the unoccupied factors and the odds on S intersect T into the positive weight. The remaining two nonempty odds products are increasing and strictly increasing in the interval interior. The lattice minor is their unnormalized weighted covariance. Twice that covariance is the double integral of the positive weight product times the two differences. The integrand is nonnegative everywhere and strictly positive at two distinct interior points; continuity makes its integral strictly positive. This statement proves the integral law. Identifying that law with a specified Markov trajectory requires its separate forward-equation bridge."))), DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("single-entry-mixture-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Pos(Formula a) => Rel(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Statement()
    {
        Formula i = F.Id("i"), u = F.Id("u"), t = F.Id("t"), h = F.Id("h"), g = F.Id("g");
        Formula s = F.Id("S"), r = F.Id("T"), sites = F.Id("I");
        Formula closed = Call("Icc", D(0), t), inside = Call("Ioo", D(0), t);
        Formula gu = Call("g", i, u);
        Formula hypotheses = And(Pos(t), And(Call("ContinuousOn", h, closed),
            And(All("u", R(), Imp(Mem(u, closed), Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Call("h", u)))),
            And(All("u", R(), Imp(Mem(u, inside), Pos(Call("h", u)))),
            And(All("i", sites, Call("ContinuousOn", Call("g", i), closed)),
            And(All("i", sites, All("u", R(), Imp(Mem(u, closed),
                And(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, gu), Rel(gu, FormulaRelationOperator.LessThan, D(1)))))),
            All("i", sites, Call("StrictMonoOn", Call("g", i), closed))))))));
        Formula notSubset = And(Seq(Neg, Sp, Call("Subset", s, r)), Seq(Neg, Sp, Call("Subset", r, s)));
        Formula left = Seq(Call("mixtureMass", h, g, t, s), Sp, Call("mixtureMass", h, g, t, r));
        Formula right = Seq(Call("mixtureMass", h, g, t, Call("inter", s, r)), Sp,
            Call("mixtureMass", h, g, t, Call("union", s, r)));
        Formula body = All("h", Seq(R(), Sp, To, Sp, R()),
            All("g", Seq(sites, Sp, To, Sp, R(), Sp, To, Sp, R()),
            All("t", R(), Imp(hypotheses,
            All("S", Call("Finset", sites), All("T", Call("Finset", sites),
                Imp(notSubset, Rel(left, FormulaRelationOperator.LessThan, right))))))));
        return Disp(All("I", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", sites), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", sites), CloseBracket, Sp, body)));
    }
}
