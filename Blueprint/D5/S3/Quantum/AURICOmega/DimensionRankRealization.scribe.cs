using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class DimensionRankRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/DimensionRankRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A noncommutative ternary comparison structure of feature rank r on a preconnected, locally compact space with continuous transfer, each reading kappa x continuous at x, and a neighbourhood of a point mapped continuously and injectively into R^d exists exactly when d >= 3 and r >= 5; every such pair is realized by the unit quaternions.",
        H("Realization of the dimension and feature rank bounds"),
        Blocks(
            Node("inj-on-im-of-re-pos", "injOn_im_of_re_pos",
                "The imaginary part is injective on the open hemisphere",
                StatementSource.FromAuthor(InjOnFormula()), DescribeRole.Lemma,
                "On the set of unit quaternions q with re q > 0, the map q -> im q is injective. "
                    + "A unit quaternion satisfies re q ^ 2 + imI q ^ 2 + imJ q ^ 2 + imK q ^ 2 = 1. "
                    + "If p and q have the same imaginary part, then re p ^ 2 = re q ^ 2, and since both real parts are positive they are equal; so p = q. "
                    + "In other words, on this open hemisphere the real part is the positive square root of 1 - |im q| ^ 2."),
            Node("continuous-tri", "continuous_tri_quaternionModel",
                "The transfer of the unit quaternion model is continuous",
                StatementSource.FromAuthor(TriFormula()), DescribeRole.Lemma,
                "The transfer of quaternionModel is (x, y, z) -> x * y^-1 * z on the group of unit quaternions. "
                    + "The unit quaternions form a topological group in the subspace topology of the quaternions, so multiplication and inversion are continuous, and the transfer is continuous on the product of three copies of the group."),
            Node("continuous-kappa", "continuous_kappa_quaternionModel",
                "The reading of the unit quaternion model is continuous",
                StatementSource.FromAuthor(KappaFormula()), DescribeRole.Lemma,
                "The reading of quaternionModel is (x, y) -> (1 + <x, y>) / 2, where <x, y> is the real inner product of the quaternions. "
                    + "The inclusion of the unit quaternions into the quaternions is continuous and the real inner product is continuous, so the reading is continuous on pairs of unit quaternions."),
            Node("exists-model-iff", "exists_model_iff",
                "The pairs of dimension and feature rank that occur",
                StatementSource.FromAuthor(ExistsFormula()), DescribeRole.Theorem,
                "Let d and r be natural numbers. There is a type M in the lowest universe with a topology that is locally compact and preconnected, a ternary comparison structure C on M, a point o, a set V and a map f from M into Euclidean space of dimension d, "
                    + "such that the transfer (x, y, z) -> tri x y z is continuous on M x M x M, the reading kappa x is continuous at x for every x, C is noncommutative, C has feature rank r, V is a neighbourhood of o, and f is continuous and injective on V, "
                    + "if and only if d >= 3 and r >= 5. "
                    + "The forward implication is the dimension and feature rank bound for such structures, theorem three_le_dim_of_hasFeatureRank. "
                    + "For the converse write d = 3 + m. The unit quaternions with the transfer x * y^-1 * z and the reading (1 + <x, y>) / 2 form a noncommutative structure of feature rank five, hence of every feature rank r >= 5, since feature rank is monotone. "
                    + "The unit quaternions are the unit sphere of the quaternions, so they are compact, hence locally compact, and preconnected. "
                    + "Transfer and reading are continuous by the two lemmas above. "
                    + "Take o = 1, take for V the open hemisphere of unit quaternions of positive real part, a neighbourhood of 1, and take for f the map sending q to its three imaginary coordinates followed by m zero coordinates. "
                    + "This map is continuous, and it is injective on V by the injectivity of the imaginary part on the open hemisphere. "
                    + "The result is assembled from classical facts (the unit three-sphere is a compact connected group, and the hemisphere of positive real part is the graph of a function of the imaginary part) together with the bounds proved in this library; no novelty is claimed. "
                    + "Not stated here: which other structures realize a given pair (d, r); any manifold structure on the unit quaternions; and the examples showing that the hypotheses of the dimension and feature rank bound cannot be dropped, apart from the realizing model itself."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("dimension-rank-realization-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Unit => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula TypeZero => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Euclid(Formula n) => Call("EuclideanSpace", Reals, Call("Fin", n));
    private static Formula Instance(Formula body) => Seq(OpenBracket, body, CloseBracket);
    private static Formula Times3(Formula x) => Seq(x, Sp, Times, Sp, x, Sp, Times, Sp, x);
    private static Formula Times2(Formula x) => Seq(x, Sp, Times, Sp, x);

    private static Formula Transfer(Formula c, Formula space)
    {
        Formula p = F.Id("p");
        return Seq(Open, p, Colon, Sp, Times3(space), Close, Sp, Mapsto, Sp,
            Call("tri", c, Seq(p, Dot, D(1)), Seq(p, Dot, D(2), Dot, D(1)), Seq(p, Dot, D(2), Dot, D(2))));
    }

    private static Formula InjOnFormula()
    {
        Formula q = F.Id("q");
        Formula map = Seq(Open, q, Colon, Sp, Unit, Close, Sp, Mapsto, Sp, Call("im", q));
        Formula hemisphere = Seq(OpenBrace, q, Sp, Mid, Sp, D(0), Sp, Lt, Sp, Call("re", q), CloseBrace);
        return Disp(Call("InjOn", map, hemisphere));
    }

    private static Formula TriFormula() => Disp(Call("Continuous", Transfer(Model, Unit)));

    private static Formula KappaFormula()
    {
        Formula p = F.Id("p");
        return Disp(Call("Continuous", Seq(Open, p, Colon, Sp, Times2(Unit), Close, Sp, Mapsto, Sp,
            Call("kappa", Model, Seq(p, Dot, D(1)), Seq(p, Dot, D(2))))));
    }

    private static Formula ExistsFormula()
    {
        Formula d = F.Id("d"), r = F.Id("r"), m = F.Id("M"), c = F.Id("C"), o = F.Id("o"),
            v = F.Id("V"), f = F.Id("f"), x = F.Id("x");
        Formula and = Seq(Sp, Land, Sp);
        Formula structure = Seq(
            Exists, Sp, m, Colon, Sp, TypeZero, Comma, Sp,
            Exists, Sp, Instance(Call("TopologicalSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("LocallyCompactSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("PreconnectedSpace", m)), Comma, Sp,
            Exists, Sp, c, Colon, Sp, Call("TernaryComparison", m), Comma, Sp,
            Exists, Sp, o, Colon, Sp, m, Comma, Sp,
            Exists, Sp, v, Colon, Sp, Call("Set", m), Comma, Sp,
            Exists, Sp, f, Colon, Sp, m, Sp, To, Sp, Euclid(d), Comma, Sp,
            Call("Continuous", Transfer(c, m)), and,
            Open, Forall, Sp, x, Colon, Sp, m, Comma, Sp, Call("ContinuousAt", Call("kappa", c, x), x), Close, and,
            Call("Noncommutative", c), and,
            Call("HasFeatureRank", c, r), and,
            v, Sp, InMacro, Sp, Call("nhds", o), and,
            Call("ContinuousOn", f, v), and,
            Call("InjOn", f, v));
        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, r, Colon, Sp, Naturals, Comma, Sp,
            Open, structure, Close, Sp, Iff, Sp,
            Open, D(3), Sp, Leq, Sp, d, Sp, Land, Sp, D(5), Sp, Leq, Sp, r, Close));
    }
}
