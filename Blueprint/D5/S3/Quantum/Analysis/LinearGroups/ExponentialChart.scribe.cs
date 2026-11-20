using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.LinearGroups;

internal sealed class ExponentialChartDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/LinearGroups/ExponentialChart.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a locally compact topological group G with a continuous injective homomorphism rho into the units of a finite-dimensional real normed algebra A, the time-one map epsilon of the one-parameter subgroups is a continuous map from the Lie subalgebra L of one-parameter generators to G with rho(epsilon(X)) = exp(X), and its restriction to an open neighbourhood of 0 in L is an open embedding into G.",
        H("Exponential Chart of a Locally Compact Group in a Finite-Dimensional Algebra"),
        Blocks(
            Node("chart", "exists_exp_chart", "Exponential chart at the identity",
                StatementSource.FromAuthor(ChartFormula()),
                DescribeRole.Theorem,
                "Let A be a finite-dimensional real normed algebra, let G be a locally compact topological group and let rho be a continuous injective group homomorphism from G into the group Units(A) of invertible elements of A, with hc a proof of continuity and hi a proof of injectivity. Let L = generatorSubalgebra(rho, hc, hi) be the Lie subalgebra of one-parameter generators for rho, with the topology induced from A; val denotes the inclusion of Units(A) and of L into A, and exp is the exponential series of A. Then there is a continuous map epsilon from L to G such that val(rho(epsilon(X))) = exp(val(X)) for every X in L, and an open subset U of L containing 0 such that the restriction domRestrict(U, epsilon) of epsilon to U is an open embedding of U into G, that is, a homeomorphism of U onto an open subset of G.",
                "Injectivity of rho makes epsilon unique: epsilon(X) is the only element of G whose image under rho is exp(X), namely the value at time 1 of the one-parameter subgroup with generator X, and in particular epsilon(0) is the identity. Two familiar local properties of the exponential map are immediate consequences of the open embedding: epsilon is injective on the neighbourhood U of 0, and epsilon maps every neighbourhood of 0 in L onto a neighbourhood of the identity in G, because it maps the open sets of L contained in U onto open sets of G.",
                "The theorem is therefore a chart of G at the identity modelled on the real vector space L, which is finite-dimensional as a subspace of A. A further consequence, which is not among the formal statements of this document: composing the chart with left translations gives charts at every point, so G is locally Euclidean with model space L, in the sense that every point of G has an open neighbourhood homeomorphic to an open subset of the finite-dimensional real vector space L. Neither a manifold structure nor a Lie group structure on G is assumed. The classical statement is the closed-subgroup theorem of J. von Neumann for closed subgroups of the general linear group and of E. Cartan for closed subgroups of Lie groups; here closedness of a linear group is replaced by local compactness of G together with continuity and injectivity of rho.",
                "The proof has four steps. First, a compact neighbourhood V of the identity in G has a boundary whose image under rho is compact and misses 1, so a path in G starting at the identity whose image under rho stays close to 1 never leaves V. Second, epsilon is continuous on all of L: near X1, the path t -> epsilon(t X1)^(-1) epsilon(t X) on [0, 1] has image under rho uniformly close to 1, so it ends in any prescribed compact neighbourhood of the identity. Third, images of neighbourhoods of 0 are neighbourhoods of the identity. Choose a complement C of L in A. The map (Y, B) -> exp(Y) exp(B) from L x C to A has the sum map as derivative at 0, so by the inverse function theorem every element of A near 1 factors as exp(Y) exp(B) with Y in L and B in C small. If the image of a neighbourhood of 0 were not a neighbourhood of the identity, consider the neighbourhood filter of the identity restricted to the complement of that image. Along this filter the C-components B are eventually nonzero, and by the escape lemma of the generator theory, applied along this filter, the directions B / norm(B) accumulate at a one-parameter generator of norm one lying in C, which is impossible since L and C meet only in 0. Fourth, let S be a domain around 0 on which exp has a continuous local inverse log, and let W be the interior of the image under epsilon of the points of L in S, an open neighbourhood of the identity by the third step. On U, the set of points of L in S whose image lies in W, the map epsilon is injective, and for an open set O of L contained in U the image of O is the set of points g of W with log(val(rho(g))) in O, which is open.",
                "Local compactness of G cannot be dropped from the conclusion. Let G be the additive group of rational numbers with its usual topology, A the real numbers and rho(q) = exp(q), a continuous injective homomorphism. A real X is a one-parameter generator only if t -> t X has a continuous lift into the rationals, which forces X = 0, since a continuous map from the real line into the rationals is constant. So the generators form the single point 0, and no map from it restricts to an open embedding of a neighbourhood of 0: the image would be a single point of the rationals, which is not open."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role,
        params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("exponential-chart-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks([.. paragraphs.Select(p => Paragraph(Text(p)))]), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);

    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Instance(Formula cls) => Seq(OpenBracket, cls, CloseBracket, Comma, Esc);

    private static Formula ChartFormula()
    {
        Formula a = F.Id("A"), g = F.Id("G"), rho = F.Id("rho"), hc = F.Id("hc"), hi = F.Id("hi");
        Formula eps = F.Id("epsilon"), x = F.Id("X"), u = F.Id("U");
        Formula sub = Call("generatorSubalgebra", rho, hc, hi);
        Formula chart = Exists("U", Call("Set", sub), And(
            Call("IsOpen", u),
            And(
                Rel(D(0), FormulaRelationOperator.MemberOf, u),
                Call("IsOpenEmbedding", Call("domRestrict", u, eps)))));
        Formula body = Exists("epsilon", Arrow(sub, g), And(
            Call("Continuous", eps),
            And(
                ForAll("X", sub, Equal(Call("val", At(rho, At(eps, x))), Call("exp", Call("val", x)))),
                chart)));
        return Disp(ForAll("A", TypeStar, Seq(
            Instance(Call("NormedRing", a)),
            ForAll("G", TypeStar, Seq(
                Instance(Call("TopologicalSpace", g)),
                Instance(Call("Group", g)),
                Instance(Call("NormedAlgebra", Reals, a)),
                Instance(Call("FiniteDimensional", Reals, a)),
                Instance(Call("IsTopologicalGroup", g)),
                Instance(Call("LocallyCompactSpace", g)),
                ForAll("rho", Call("MonoidHom", g, Call("Units", a)),
                    ForAll("hc", Call("Continuous", rho),
                        ForAll("hi", Call("Injective", rho), body))))))));
    }
}
