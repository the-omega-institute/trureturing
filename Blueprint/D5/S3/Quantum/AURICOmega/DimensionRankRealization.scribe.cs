using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class DimensionRankRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/DimensionRankRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For natural numbers d and r, three conditions are equivalent: a noncommutative ternary comparison structure of feature rank at most r exists on a preconnected, locally compact space with continuous transfer, each reading kappa x continuous at x, and a neighbourhood of a point mapped continuously and injectively into R^d; such a structure exists on a compact, Hausdorff, connected space with jointly continuous reading and a continuous map into R^d injective on an open set containing the point; and d >= 3 and r >= 5. The unit quaternions realize every such pair.",
        H("Realization of the dimension and feature rank bounds"),
        Blocks(
            Node("inj-on-im-of-re-nonneg", "injOn_im_of_re_nonneg",
                "The imaginary part is injective on the closed hemisphere",
                StatementSource.FromAuthor(InjOnFormula()), DescribeRole.Lemma,
                "On the set of unit quaternions q with 0 <= re q, the map q -> im q is injective. "
                    + "A unit quaternion satisfies re q ^ 2 + imI q ^ 2 + imJ q ^ 2 + imK q ^ 2 = 1. "
                    + "If p and q have the same imaginary part, then re p ^ 2 = re q ^ 2, and since both real parts are nonnegative they are equal; so p = q. "
                    + "In other words, on this closed hemisphere the real part is the nonnegative square root of 1 - |im q| ^ 2. "
                    + "The closed hemisphere cannot be enlarged: a unit quaternion q with re q < 0 has the same imaginary part as the quaternion -re q + im q of the hemisphere."),
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
            Node("exists-model-tfae", "exists_model_tfae",
                "Three equivalent conditions on the pairs of dimension and feature rank",
                StatementSource.FromAuthor(ExistsFormula()), DescribeRole.Theorem,
                "Let d and r be natural numbers. Here C has feature rank r means that the reading kappa x y is the inner product of phi x and phi y for some map phi from M into Euclidean space of dimension r; so it says that C has feature rank at most r. The following three conditions are equivalent. "
                    + "(1) There is a type M in the lowest universe with a topology that is locally compact and preconnected, a ternary comparison structure C on M, a point o, a set V and a map f from M into Euclidean space of dimension d, "
                    + "such that the transfer (x, y, z) -> tri x y z is continuous on M x M x M, the reading kappa x is continuous at x for every x, C is noncommutative, C has feature rank r, V is a neighbourhood of o, and f is continuous on V and injective on V. "
                    + "(2) There is a type M in the lowest universe with a topology that is compact, Hausdorff and connected, a ternary comparison structure C on M, a point o, a set V and a map f from M into Euclidean space of dimension d, "
                    + "such that the transfer is continuous on M x M x M, the reading (x, y) -> kappa x y is continuous on M x M, C is noncommutative, C has feature rank r, V is open and contains o, f is continuous on M, and f is injective on V. "
                    + "(3) d >= 3 and r >= 5. "
                    + "Condition (2) implies condition (1): a compact Hausdorff space is locally compact, a connected space is preconnected, joint continuity of the reading gives continuity of kappa x at x, an open set containing o is a neighbourhood of o, and a continuous map is continuous on V. "
                    + "Condition (1) implies condition (3) by the dimension and feature rank bound for such structures, theorem three_le_dim_of_hasFeatureRank. "
                    + "For condition (3) implies condition (2) write d = 3 + m. The unit quaternions with the transfer x * y^-1 * z and the reading (1 + <x, y>) / 2 form a noncommutative structure of feature rank five, hence of feature rank at most r for every r >= 5, since feature rank is monotone. "
                    + "The unit quaternions are the unit sphere of the quaternions, so they are compact, Hausdorff, and connected. "
                    + "Transfer and reading are continuous by the two lemmas above. "
                    + "Take o = 1, take for V the open hemisphere of unit quaternions of positive real part, an open set containing 1, and take for f the map sending q to its three imaginary coordinates followed by m zero coordinates. "
                    + "This map is continuous on all unit quaternions, and it is injective on V because V lies in the closed hemisphere, on which the imaginary part is injective. "
                    + "So the bounds d >= 3 and r >= 5 are attained, and they are attained already in the more restrictive class of condition (2). "
                    + "The result is assembled from classical facts (the unit three-sphere is a compact connected group, and the hemisphere of nonnegative real part is the graph of a function of the imaginary part) together with the bounds proved in this library; no novelty is claimed. "
                    + "Not stated here: which other structures realize a given pair (d, r); any manifold structure on the unit quaternions; and examples showing that individual hypotheses of the dimension and feature rank bound cannot be dropped."))));

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
        Formula hemisphere = Seq(OpenBrace, q, Sp, Mid, Sp, D(0), Sp, Leq, Sp, Call("re", q), CloseBrace);
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
            v = F.Id("V"), f = F.Id("f"), x = F.Id("x"), p = F.Id("p");
        Formula and = Seq(Sp, Land, Sp);
        Formula witnesses = Seq(
            Exists, Sp, c, Colon, Sp, Call("TernaryComparison", m), Comma, Sp,
            Exists, Sp, o, Colon, Sp, m, Comma, Sp,
            Exists, Sp, v, Colon, Sp, Call("Set", m), Comma, Sp,
            Exists, Sp, f, Colon, Sp, m, Sp, To, Sp, Euclid(d), Comma, Sp);
        Formula weak = Seq(
            Exists, Sp, m, Colon, Sp, TypeZero, Comma, Sp,
            Exists, Sp, Instance(Call("TopologicalSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("LocallyCompactSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("PreconnectedSpace", m)), Comma, Sp,
            witnesses,
            Call("Continuous", Transfer(c, m)), and,
            Open, Forall, Sp, x, Colon, Sp, m, Comma, Sp, Call("ContinuousAt", Call("kappa", c, x), x), Close, and,
            Call("Noncommutative", c), and,
            Call("HasFeatureRank", c, r), and,
            v, Sp, InMacro, Sp, Call("nhds", o), and,
            Call("ContinuousOn", f, v), and,
            Call("InjOn", f, v));
        Formula strong = Seq(
            Exists, Sp, m, Colon, Sp, TypeZero, Comma, Sp,
            Exists, Sp, Instance(Call("TopologicalSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("CompactSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("T2Space", m)), Comma, Sp,
            Exists, Sp, Instance(Call("ConnectedSpace", m)), Comma, Sp,
            witnesses,
            Call("Continuous", Transfer(c, m)), and,
            Call("Continuous", Seq(Open, p, Colon, Sp, Times2(m), Close, Sp, Mapsto, Sp,
                Call("kappa", c, Seq(p, Dot, D(1)), Seq(p, Dot, D(2))))), and,
            Call("Noncommutative", c), and,
            Call("HasFeatureRank", c, r), and,
            Call("IsOpen", v), and,
            o, Sp, InMacro, Sp, v, and,
            Call("Continuous", f), and,
            Call("InjOn", f, v));
        Formula bounds = Seq(D(3), Sp, Leq, Sp, d, Sp, Land, Sp, D(5), Sp, Leq, Sp, r);
        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, r, Colon, Sp, Naturals, Comma, Sp,
            Call("TFAE", Seq(OpenBracket, weak, Comma, Sp, strong, Comma, Sp, bounds, CloseBracket))));
    }
}
