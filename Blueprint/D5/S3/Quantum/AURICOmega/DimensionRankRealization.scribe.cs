using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class DimensionRankRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/DimensionRankRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For natural numbers d and r, four conditions are equivalent, with carriers in an arbitrary universe: a noncommutative ternary comparison structure of feature rank at most r exists on a preconnected, locally compact space with continuous transfer, each reading kappa x continuous at x, and a neighbourhood of a point mapped continuously and injectively into R^d; such a structure exists on a compact, Hausdorff, path-connected space with jointly continuous reading and a continuous map into R^d injective on an open set containing the point; d >= 3 and r >= 5; and the unit quaternion model has feature rank at most r and admits a continuous map into R^d injective on an open set containing 1. So the unit quaternions realize every such pair. The imaginary part is injective on a set S of unit quaternions exactly when every q in S with -star q in S has real part zero, and the closed hemisphere of nonnegative real part is the largest set that contains the open hemisphere and on which the imaginary part is injective.",
        H("Realization of the dimension and feature rank bounds"),
        Blocks(
            Node("inj-on-im-iff", "injOn_im_iff",
                "The sets on which the imaginary part is injective",
                StatementSource.FromAuthor(InjOnIffFormula()), DescribeRole.Theorem,
                "In this document re q and im q denote the real part and the imaginary part of the quaternion underlying a unit quaternion q, that is, of the image of q in the quaternions. "
                    + "Let S be a set of unit quaternions. The map q -> im q is injective on S if and only if every q in S with -star q in S has re q = 0. "
                    + "The unit quaternion -star q has real part -re q and the same imaginary part as q. "
                    + "If the imaginary part is injective on S and both q and -star q lie in S, then q = -star q, so re q = -re q and re q = 0. "
                    + "Conversely, a unit quaternion satisfies re q ^ 2 + imI q ^ 2 + imJ q ^ 2 + imK q ^ 2 = 1, so two unit quaternions p and q with the same imaginary part have re p ^ 2 = re q ^ 2. "
                    + "Then either re p = re q, and p = q, or re p = -re q, and p = -star q; in the second case q and -star q both lie in S, so re q = 0, hence re p = re q and again p = q. "
                    + "So the imaginary part fails to be injective on S exactly when S contains a pair q, -star q with re q different from zero, and such a pair has a common imaginary part."),
            Node("is-greatest-inj-on-im", "isGreatest_injOn_im",
                "The closed hemisphere is the largest set of injectivity of the imaginary part",
                StatementSource.FromAuthor(IsGreatestFormula()), DescribeRole.Proposition,
                "Consider the sets S of unit quaternions that contain the open hemisphere of unit quaternions q with 0 < re q and on which the map q -> im q is injective. "
                    + "The closed hemisphere of unit quaternions q with 0 <= re q is the largest of these sets: it is one of them, and it contains each of them. "
                    + "It is one of them by the preceding theorem, since 0 <= re q and 0 <= re(-star q) = -re q force re q = 0. "
                    + "If S is one of these sets and some q in S had re q < 0, then -star q would lie in the open hemisphere, hence in S, and the preceding theorem would give re q = 0, which is impossible. "
                    + "In particular the imaginary part is injective on the closed hemisphere: there the real part is the nonnegative square root of 1 - |im q| ^ 2."),
            Node("continuous-tri", "continuous_tri_quaternionModel",
                "The transfer of the unit quaternion model is continuous",
                StatementSource.FromAuthor(TriFormula()), DescribeRole.Lemma,
                "The transfer of quaternionModel is (x, y, z) -> x * y^-1 * z on the group of unit quaternions. "
                    + "The unit quaternions form a topological group in the subspace topology of the quaternions, so multiplication and inversion are continuous, and the transfer is continuous on the product of three copies of the group."),
            Node("exists-model-tfae", "exists_model_tfae",
                "Four equivalent conditions on the pairs of dimension and feature rank",
                StatementSource.FromAuthor(ExistsFormula()), DescribeRole.Theorem,
                "Let d and r be natural numbers and let u be a universe level; the types M in conditions (1) and (2) range over Type u. Here C has feature rank r means that the reading kappa x y is the inner product of phi x and phi y for some map phi from M into Euclidean space of dimension r; so it says that C has feature rank at most r. The following four conditions are equivalent. "
                    + "(1) There is a type M with a topology that is locally compact and preconnected, a ternary comparison structure C on M, a point o, a set V and a map f from M into Euclidean space of dimension d, "
                    + "such that the transfer (x, y, z) -> tri x y z is continuous on M x M x M, the reading kappa x is continuous at x for every x, C is noncommutative, C has feature rank r, V is a neighbourhood of o, and f is continuous on V and injective on V. "
                    + "(2) There is a type M with a topology that is compact, Hausdorff and path-connected, a ternary comparison structure C on M, a point o, a set V and a map f from M into Euclidean space of dimension d, "
                    + "such that the transfer is continuous on M x M x M, the reading (x, y) -> kappa x y is continuous on M x M, C is noncommutative, C has feature rank r, V is open and contains o, f is continuous on M, and f is injective on V. "
                    + "(3) d >= 3 and r >= 5. "
                    + "(4) The unit quaternion model quaternionModel has feature rank r, and there are a set V of unit quaternions and a map f from the unit quaternions into Euclidean space of dimension d such that V is open and contains 1, f is continuous, and f is injective on V. "
                    + "Condition (2) implies condition (1): a compact Hausdorff space is locally compact, a path-connected space is preconnected, joint continuity of the reading gives continuity of kappa x at x, an open set containing o is a neighbourhood of o, and a continuous map is continuous on V. "
                    + "Condition (1) implies condition (3) by the dimension and feature rank bound for such structures, theorem three_le_dim_of_hasFeatureRank, which holds for carriers in every universe. "
                    + "For condition (3) implies condition (4) write d = 3 + m. The unit quaternions with the transfer x * y^-1 * z and the reading (1 + <x, y>) / 2 form a noncommutative structure of feature rank five, hence of feature rank at most r for every r >= 5, since feature rank is monotone. "
                    + "Take for V the open hemisphere of unit quaternions of positive real part, an open set containing 1, and take for f the map sending q to its three imaginary coordinates followed by m zero coordinates. "
                    + "This map is continuous on all unit quaternions, and it is injective on the closed hemisphere by the preceding proposition, hence on V. "
                    + "For condition (4) implies condition (2) take for M the lift ULift of the unit quaternions to the universe u, with the topology induced by the projection onto the unit quaternions, and carry the unit quaternion model, the point 1, the set V and the map f along this projection. "
                    + "The lift is homeomorphic to the unit quaternions, which are compact and Hausdorff, being the unit sphere of the quaternions, and path-connected, by the lemma that the unit quaternions are path-connected. "
                    + "The carried structure is noncommutative and has feature rank r, its transfer is continuous by the lemma above, its reading is continuous by the lemma that the reading of the unit quaternion model is continuous, and openness, continuity and injectivity pass along the homeomorphism. "
                    + "So the unit quaternions realize every pair d >= 3, r >= 5, as condition (4) states, and the pairs are attained already in the more restrictive class of condition (2), in every universe. "
                    + "In condition (2) the requirement that M be Hausdorff follows from the joint continuity of the reading: kappa x y = 1 holds exactly when x = y, so the diagonal of M x M is the preimage of 1 under the continuous reading and is closed. This remark is not stated as a theorem here. "
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
    private static Formula TypeU => Seq(Operatorname, Grp(F.Id("Type")), Sp, F.Id("u"));
    private static Formula Euclid(Formula n) => Call("EuclideanSpace", Reals, Call("Fin", n));
    private static Formula Instance(Formula body) => Seq(OpenBracket, body, CloseBracket);
    private static Formula Times3(Formula x) => Seq(x, Sp, Times, Sp, x, Sp, Times, Sp, x);
    private static Formula Times2(Formula x) => Seq(x, Sp, Times, Sp, x);
    private static Formula And => Seq(Sp, Land, Sp);

    private static Formula Transfer(Formula c, Formula space)
    {
        Formula p = F.Id("p");
        return Seq(Open, p, Colon, Sp, Times3(space), Close, Sp, Mapsto, Sp,
            Call("tri", c, Seq(p, Dot, D(1)), Seq(p, Dot, D(2), Dot, D(1)), Seq(p, Dot, D(2), Dot, D(2))));
    }

    private static Formula ImMap()
    {
        Formula q = F.Id("q");
        return Seq(Open, q, Colon, Sp, Unit, Close, Sp, Mapsto, Sp, Call("im", q));
    }

    private static Formula InjOnIffFormula()
    {
        Formula q = F.Id("q"), s = F.Id("S");
        Formula condition = Seq(
            Open, Forall, Sp, q, Sp, InMacro, Sp, s, Comma, Sp,
            Minus, Call("star", q), Sp, InMacro, Sp, s, Sp, To, Sp,
            Call("re", q), Sp, Eq, Sp, D(0), Close);
        return Disp(Seq(
            Forall, Sp, s, Colon, Sp, Call("Set", Unit), Comma, Sp,
            Call("InjOn", ImMap(), s), Sp, Iff, Sp, condition));
    }

    private static Formula IsGreatestFormula()
    {
        Formula q = F.Id("q"), s = F.Id("S");
        Formula open = Seq(OpenBrace, q, Colon, Sp, Unit, Sp, Mid, Sp, D(0), Sp, Lt, Sp, Call("re", q), CloseBrace);
        Formula family = Seq(
            OpenBrace, s, Colon, Sp, Call("Set", Unit), Sp, Mid, Sp,
            open, Sp, Subseteq, Sp, s, And, Call("InjOn", ImMap(), s), CloseBrace);
        Formula closed = Seq(OpenBrace, q, Sp, Mid, Sp, D(0), Sp, Leq, Sp, Call("re", q), CloseBrace);
        return Disp(Call("IsGreatest", family, closed));
    }

    private static Formula TriFormula() => Disp(Call("Continuous", Transfer(Model, Unit)));

    private static Formula ExistsFormula()
    {
        Formula d = F.Id("d"), r = F.Id("r"), m = F.Id("M"), c = F.Id("C"), o = F.Id("o"),
            v = F.Id("V"), f = F.Id("f"), x = F.Id("x"), p = F.Id("p");
        Formula witnesses = Seq(
            Exists, Sp, c, Colon, Sp, Call("TernaryComparison", m), Comma, Sp,
            Exists, Sp, o, Colon, Sp, m, Comma, Sp,
            Exists, Sp, v, Colon, Sp, Call("Set", m), Comma, Sp,
            Exists, Sp, f, Colon, Sp, m, Sp, To, Sp, Euclid(d), Comma, Sp);
        Formula weak = Seq(
            Exists, Sp, m, Colon, Sp, TypeU, Comma, Sp,
            Exists, Sp, Instance(Call("TopologicalSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("LocallyCompactSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("PreconnectedSpace", m)), Comma, Sp,
            witnesses,
            Call("Continuous", Transfer(c, m)), And,
            Open, Forall, Sp, x, Colon, Sp, m, Comma, Sp, Call("ContinuousAt", Call("kappa", c, x), x), Close, And,
            Call("Noncommutative", c), And,
            Call("HasFeatureRank", c, r), And,
            v, Sp, InMacro, Sp, Call("nhds", o), And,
            Call("ContinuousOn", f, v), And,
            Call("InjOn", f, v));
        Formula strong = Seq(
            Exists, Sp, m, Colon, Sp, TypeU, Comma, Sp,
            Exists, Sp, Instance(Call("TopologicalSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("CompactSpace", m)), Comma, Sp,
            Exists, Sp, Instance(Call("T2Space", m)), Comma, Sp,
            Exists, Sp, Instance(Call("PathConnectedSpace", m)), Comma, Sp,
            witnesses,
            Call("Continuous", Transfer(c, m)), And,
            Call("Continuous", Seq(Open, p, Colon, Sp, Times2(m), Close, Sp, Mapsto, Sp,
                Call("kappa", c, Seq(p, Dot, D(1)), Seq(p, Dot, D(2))))), And,
            Call("Noncommutative", c), And,
            Call("HasFeatureRank", c, r), And,
            Call("IsOpen", v), And,
            o, Sp, InMacro, Sp, v, And,
            Call("Continuous", f), And,
            Call("InjOn", f, v));
        Formula bounds = Seq(D(3), Sp, Leq, Sp, d, Sp, Land, Sp, D(5), Sp, Leq, Sp, r);
        Formula quaternion = Seq(
            Exists, Sp, v, Colon, Sp, Call("Set", Unit), Comma, Sp,
            Exists, Sp, f, Colon, Sp, Unit, Sp, To, Sp, Euclid(d), Comma, Sp,
            Call("HasFeatureRank", Model, r), And,
            Call("IsOpen", v), And,
            D(1), Sp, InMacro, Sp, v, And,
            Call("Continuous", f), And,
            Call("InjOn", f, v));
        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, r, Colon, Sp, Naturals, Comma, Sp,
            Call("TFAE", Seq(OpenBracket, weak, Comma, Sp, strong, Comma, Sp, bounds, Comma, Sp,
                quaternion, CloseBracket))));
    }
}
