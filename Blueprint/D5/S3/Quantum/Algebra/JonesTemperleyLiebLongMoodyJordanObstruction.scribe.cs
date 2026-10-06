using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class JonesTemperleyLiebLongMoodyJordanObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/negami2026middle");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negami (arXiv:2610.00293, Problem 6.8) asks for a proof of the Jordan obstruction observed numerically for Katz-Long-Moody seeds built from the endpoint sectors of the Jones-Temperley-Lieb path representations. For every n >= 3, every level ell >= 4 and every endpoint sector of dimension at least two, every seed generator g_j has no fixed vector, so K = 0, and the ambient Long-Moody operator S_1 has a Jordan chain of length two at the eigenvalue -alpha^(-3).",
        H("The Jordan obstruction for the Jones-Temperley-Lieb endpoint-sector seeds"),
        Blocks(
            Node("adjacency", "The A graph", AdjacencyFormula(),
                "Vertices are the elements of Fin(ell - 1); vertex a is the paper's vertex a + 1 of the A_(ell-1) graph, and two vertices are adjacent when their labels differ by one.",
                "adj", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weights", "The Perron-Frobenius weights", WeightFormula(),
                "mu(a) = sin((a + 1) pi/ell), the standard path-model weight of vertex a + 1.",
                "mu", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("loop", "The loop value", LoopFormula(),
                "delta_ell = 2 cos(pi/ell), the value with E_i^2 = delta_ell E_i.",
                "delta", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("start", "The left endpoint", StartFormula(),
                "The first vertex, the paper's vertex 1, at which every path starts.",
                "v1", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sector", "The endpoint sectors", SectorFormula(),
                "Sector(ell, n, t) is the basis of the endpoint sector of the length-(n + 1) paths on the A graph that start at the left endpoint and end at t, the frozen LegalPath type.",
                "Sector", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tl", "The path-model Temperley-Lieb operators", TemperleyLiebFormula(),
                "E_j, for j < n, is delta times the frozen weighted path projection at interior vertex j + 1: it vanishes unless the vertices j and j + 2 of the path agree at some c, and then replaces vertex j + 1 by each neighbour d of c with coefficient sqrt(mu(h) mu(d))/mu(c). For j >= n it is 0.",
                "E", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phase", "The braid phase", PhaseFormula(),
                "alpha_ell = i exp(-pi i/(2 ell)), with beta_ell = alpha_ell^(-1) and no additional scalar twist.",
                "alpha", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("braid", "The braid generators", BraidFormula(),
                "rho(sigma_j) = alpha I + alpha^(-1) E_j on an endpoint sector.",
                "rho", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("braidseed", "The seed braid generators", SeedBraidFormula(),
                "s_i = rho(sigma_i), the action of the braid generators of B_n inside B_(n+1).",
                "s", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seedrec", "The seed free generators", SeedFormula(),
                "The images of x_1 = sigma_0^2 and x_(j+1) = sigma_j x_j sigma_j^(-1), zero-based: seed(0) = rho(0)^2 and seed(j + 1) = s(j + 1) seed(j) s(j + 1)^(-1).",
                "seed", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("free", "The free-group images", FreeFormula(),
                "g(j) for j in Fin(n) is seed(j), the paper's g_(j+1) = rho(x_(j+1)).",
                "g", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("longmoody", "The ambient Long-Moody operator", LongMoodyFormula(),
                "Eq. (braid-matrices) at i = 1 on n slots, zero-based: on slots 0 and 1 the block s_1 (0, g_1; I, I - g_2), and s_1 on every other slot. In the formula S1 is written with entries indexed by (slot, path).",
                "S1", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("eigen", "The eigenvalue", EigenvalueFormula(),
                "b(ell) = -alpha_ell^(-3), the eigenvalue of rho(sigma_j) on the image of E_j.",
                "b", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The Jordan obstruction", ClaimFormula(),
                "For every ell >= 4, n >= 3 and end vertex t whose sector has at least two paths (in the formula h is the proof of 2 <= ell obtained from ell >= 4, which the sector and the operators take as an argument): no seed generator g_j has a nonzero fixed vector (so K = 0, the sectors admitted by the remark's test), and S_1 - b is not semisimple at b: some w has (S_1 - b)^2 w = 0 and (S_1 - b) w != 0.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The Jordan obstruction holds for every endpoint sector", Disp(F.Id("claim")),
                "Put a = alpha_ell, delta = 2 cos(pi/ell) = -(a^2 + a^(-2)). The weights satisfy sum over neighbours of mu = delta mu (the boundary terms sin 0 and sin pi vanish), so the frozen Temperley-Lieb theorem gives E_j^2 = delta E_j and (rho_j - a)(rho_j + a^(-3)) = 0. Hence every g_j satisfies (g - a^2)(g - a^(-6)) = 0, and since ell >= 4 neither a^2 nor a^(-6) is 1, so g_j has no fixed vector. A sector with two paths contains a path beginning 1, 2, 1 and the same path with its vertex 2 replaced by 3 (vertex 3 exists as ell >= 4); on their span rho_0 and rho_1 act, in a suitable basis f_0, f_1, by (-a^(-3), a; 0, a) and (a, 0; a^(-3), -a^(-3)). On the four-dimensional subspace of slots 0 and 1 the operator S_1 is (0, UG; U, U(I - H)) with U = rho_1, G = rho_0^2, H = U G U^(-1), and an explicit Laurent-polynomial vector w gives (S_1 - b)^2 w = 0 and (S_1 - b) w = (a^6 - 1) times a nonzero vector, which is nonzero as a^6 != 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("negami-2026-jones-temperley-lieb-jordan-obstruction"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("jtljordan-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Forall, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula a, Formula type, Formula body) =>
        Seq(Exists, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula PlusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MinusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula TimesOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Inverse(Formula a) => Power(a, Seq(Minus, F.D(1)));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula L() => Ell;
    private static Formula N() => F.Id("n");
    private static Formula T() => F.Id("t");
    private static Formula Hp() => F.Id("h");
    private static Formula TwoLeq() => Parenthesized(Leq(F.D(2), L()));
    private static Formula Vertices() => Call("Fin", MinusOf(L(), F.D(1)));
    private static Formula Sector() => Call("Sector", L(), N(), Hp(), T());
    private static Formula Start() => Call("v1", L(), Hp());
    private static Formula Op(string name, params Formula[] extra) =>
        Call(name, [L(), N(), Hp(), T(), .. extra]);
    private static Formula Scaled(Formula c, Formula m) => Seq(c, Sp, Cdot, Sp, m);
    private static Formula Hyps(Formula body) =>
        All(L(), Naturals(), All(N(), Naturals(), All(Hp(), TwoLeq(), All(T(), Vertices(), body))));

    private static Formula AdjacencyFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula rel = Or(Equal(PlusOf(Call("val", a), F.D(1)), Call("val", b)),
            Equal(PlusOf(Call("val", b), F.D(1)), Call("val", a)));
        return Disp(All(L(), Naturals(), All(a, Vertices(), All(b, Vertices(),
            Iff(Call("adj", L(), a, b), rel)))));
    }

    private static Formula WeightFormula()
    {
        Formula a = F.Id("a");
        Formula value = Call("sin", new Formula.Fraction(TimesOf(Parenthesized(PlusOf(Call("val", a), F.D(1))), Pi), L()));
        return Disp(All(L(), Naturals(), All(a, Vertices(), Equal(Call("mu", L(), a), value))));
    }

    private static Formula LoopFormula() =>
        Disp(All(L(), Naturals(), Equal(Call("delta", L()), TimesOf(F.D(2), Call("cos", new Formula.Fraction(Pi, L()))))));

    private static Formula StartFormula() =>
        Disp(All(L(), Naturals(), All(Hp(), TwoLeq(), Equal(Call("val", Start()), F.D(0)))));

    private static Formula SectorFormula() =>
        Disp(Hyps(Equal(Sector(), Call("LegalPath", Call("adj", L()), PlusOf(N(), F.D(1)), Start(), T()))));

    private static Formula TemperleyLiebFormula()
    {
        Formula j = F.Id("j");
        Formula projection = Call("pathProjection", Call("adj", L()), Call("mu", L()), Call("delta", L()),
            PlusOf(N(), F.D(1)), Start(), T(), PlusOf(j, F.D(1)));
        Formula value = Call("ite", Less(j, N()), Scaled(Call("delta", L()), projection), F.D(0));
        return Disp(Hyps(All(j, Naturals(), Equal(Op("E", j), value))));
    }

    private static Formula PhaseFormula()
    {
        Formula exponent = new Formula.Fraction(Seq(Minus, Pi, Sp, F.Id("i")), TimesOf(F.D(2), L()));
        return Disp(All(L(), Naturals(), Equal(Call("alpha", L()), TimesOf(F.Id("i"), Call("exp", exponent)))));
    }

    private static Formula BraidFormula()
    {
        Formula j = F.Id("j");
        Formula a = Call("alpha", L());
        Formula value = PlusOf(Scaled(a, F.D(1)), Scaled(Inverse(a), Op("E", j)));
        return Disp(Hyps(All(j, Naturals(), Equal(Op("rho", j), value))));
    }

    private static Formula SeedBraidFormula()
    {
        Formula i = F.Id("i");
        return Disp(Hyps(All(i, Naturals(), Equal(Op("s", i), Op("rho", i)))));
    }

    private static Formula SeedFormula()
    {
        Formula j = F.Id("j");
        Formula first = Equal(Op("seed", F.D(0)), TimesOf(Op("rho", F.D(0)), Op("rho", F.D(0))));
        Formula next = All(j, Naturals(), Equal(Op("seed", PlusOf(j, F.D(1))),
            TimesOf(TimesOf(Op("s", PlusOf(j, F.D(1))), Op("seed", j)), Inverse(Op("s", PlusOf(j, F.D(1)))))));
        return Disp(Hyps(And(first, next)));
    }

    private static Formula FreeFormula()
    {
        Formula j = F.Id("j");
        return Disp(Hyps(All(j, Call("Fin", N()), Equal(Op("g", j), Op("seed", Call("val", j))))));
    }

    private static Formula LongMoodyFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l"), x = F.Id("x"), y = F.Id("y");
        Formula u = Op("s", F.D(1)), gOne = Op("seed", F.D(0)), gTwo = Op("seed", F.D(1));
        Formula entry = new Formula.Apply(Op("S1"), [Parenthesized(Seq(k, Comma, Sp, x)), Parenthesized(Seq(l, Comma, Sp, y))]);
        Formula at(Formula m) => new Formula.Apply(Parenthesized(m), [x, y]);
        Formula slot(Formula a, byte v) => Equal(Call("val", a), F.D(v));
        Formula value = Call("ite", And(slot(k, 0), slot(l, 1)), at(TimesOf(u, gOne)),
            Call("ite", And(slot(k, 1), slot(l, 0)), at(u),
                Call("ite", And(slot(k, 1), slot(l, 1)), at(TimesOf(u, Parenthesized(MinusOf(F.D(1), gTwo)))),
                    Call("ite", And(Leq(F.D(2), Call("val", k)), Equal(k, l)), at(u), F.D(0)))));
        return Disp(Hyps(All(k, Call("Fin", N()), All(l, Call("Fin", N()), All(x, Sector(), All(y, Sector(),
            Equal(entry, value)))))));
    }

    private static Formula EigenvalueFormula() =>
        Disp(All(L(), Naturals(), Equal(Call("b", L()), Seq(Minus, Power(Parenthesized(Inverse(Call("alpha", L()))), F.D(3))))));

    private static Formula ClaimFormula()
    {
        Formula j = F.Id("j"), v = F.Id("v"), w = F.Id("w");
        Formula shifted = MinusOf(Op("S1"), Scaled(Call("b", L()), F.D(1)));
        Formula noFixed = All(j, Call("Fin", N()), All(v, Seq(Sector(), Sp, To, Sp, Complexes()),
            Implies(Equal(Call("mulVec", Op("g", j), v), v), Equal(v, F.D(0)))));
        Formula once = Call("mulVec", shifted, w);
        Formula jordan = Some(w, Seq(Parenthesized(Seq(Call("Fin", N()), Sp, Times, Sp, Sector())), Sp, To, Sp, Complexes()),
            And(Equal(Call("mulVec", shifted, once), F.D(0)), NotEqual(once, F.D(0))));
        Formula body = Implies(Leq(F.D(4), L()), Implies(Leq(F.D(3), N()),
            Implies(Leq(F.D(2), Call("card", Sector())), And(noFixed, jordan))));
        return Disp(Iff(F.Id("claim"), All(L(), Naturals(), All(N(), Naturals(), All(T(), Vertices(), body)))));
    }
}
