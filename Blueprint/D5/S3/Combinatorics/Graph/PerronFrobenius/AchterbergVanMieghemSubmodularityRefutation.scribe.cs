using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PerronFrobenius;

internal sealed class AchterbergVanMieghemSubmodularityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/achterbergvanmieghem2025spectral");
    private const string DefinitionQuote =
        "“The spectral degree exponent (SDE) of a simple, undirected, non-regular "
        + "(but possibly disconnected and weighted) graph G is defined as the solution for q "
        + "of the equation λ₁ = ((1/N) Σ_{i=1}^N d_i^q)^{1/q}.” "
        + "(Definition 2.1, equation (2.1), p. 1.) ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-vertex graphs refute edge-set submodularity of the spectral degree exponent.",
        H("The spectral degree exponent fails submodularity"),
        Blocks(
            Node("degree-power-mean", "The degree power mean", "degreePowerMean",
                MeanFormula(), DefinitionQuote
                + "Here N is n, dᵢ is SimpleGraph.degree G v, and real exponentiation is Real.rpow. "
                + "The sum ranges over all v : Fin n; division and powers take place in ℝ.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("regular", "Regular graphs", "IsRegular", RegularFormula(),
                DefinitionQuote + "Regularity means that there is a natural number r "
                + "such that every vertex has degree r, expressed by SimpleGraph.IsRegularOfDegree.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spectral-degree-exponent", "Finite spectral degree exponents", "IsSpectralDegreeExponent",
                ExponentFormula(), DefinitionQuote
                + "“The spectral degree exponent (SDE) exists, is unique and is bounded in "
                + "q ∈ [2, ∞].” (Theorem 2.2, p. 2.) The displayed predicate selects finite real "
                + "solutions q ≥ 2 for non-regular unweighted graphs. “The spectral radius λ₁ is "
                + "the largest eigenvalue of the weighted adjacency matrix A of the graph G.” (p. 1.) "
                + "Its real adjacency spectrum has supremum sSup (spectrum ℝ (G.adjMatrix ℝ)). All four graphs used below "
                + "have such solutions; no statement about infinite exponents is required.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("submodularity", "Submodularity on a fixed vertex set", "claim",
                Iff(F.Id("claim"), Parenthesized(ClaimBody())),
                "“Several other properties of the SDE have not yet been established, e.g. "
                + "whether the SDE is submodular or if the SDE can be used successfully in "
                + "applications to enhance or reduce assortativity.” (Section 7, p. 15.) "
                + "The ground set consists of possible edges on Fin n. The lattice operations "
                + "are edge union and intersection. The four real exponents satisfy their "
                + "respective equations before the submodular inequality is required.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("refutation", "A five-vertex counterexample", "result",
                new Formula.Not(Parenthesized(ClaimBody())),
                "Take E₀ = {01, 02, 03, 14, 23}, e = 24 and f = 34 on five vertices. "
                + "The exponents of E₀ and E₀ ∪ {e,f} lie strictly between 3 and 4, "
                + "whereas those of E₀ ∪ {e} and E₀ ∪ {f} lie strictly between 2 and 3. "
                + "Characteristic polynomials bound the largest eigenvalues, exact degree "
                + "moments bound the power means, and continuity supplies these finite solutions. "
                + "Thus the union and intersection exponents have sum greater than 6, "
                + "while the two single-edge additions have sum less than 6. "
                + "The source definitions and earlier theorems are unaffected.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("achterberg-van-mieghem-2025-spectral-degree-exponent-submodularity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula MeanFormula()
    {
        var g = F.Id("G");
        var q = F.Id("q");
        var n = F.Id("n");
        var v = F.Id("v");
        var degree = Parenthesized(Seq(Call("SimpleGraph.degree", g, v), Sp, Colon, Sp, Reals()));
        var moment = Seq(new Formula.Subscript(Sum, Seq(v, Sp, Colon, Sp, Call("Fin", n))), Sp,
            new Formula.Power(degree, q));
        var scale = new Formula.Fraction(D(1), Parenthesized(Seq(n, Sp, Colon, Sp, Reals())));
        return GraphBinders(All("q", Reals(), Equal(Call("degreePowerMean", g, q),
            new Formula.Power(Parenthesized(Multiply(scale, Parenthesized(moment))),
                new Formula.Fraction(D(1), q)))));
    }

    private static Formula RegularFormula() => GraphBinders(Iff(Call("IsRegular", F.Id("G")),
        Some("r", Naturals(), Call("SimpleGraph.IsRegularOfDegree", F.Id("G"), F.Id("r")))));

    private static Formula ExponentFormula()
    {
        var g = F.Id("G");
        var q = F.Id("q");
        return GraphBinders(All("q", Reals(), Iff(Call("IsSpectralDegreeExponent", g, q),
            And(new Formula.Not(Call("IsRegular", g)), And(AtMost(D(2), q),
                Equal(Call("sSup", Call("spectrum", Reals(), Call("SimpleGraph.adjMatrix", Reals(), g))),
                    Call("degreePowerMean", g, q)))))));
    }

    private static Formula ClaimBody()
    {
        var g = F.Id("G");
        var h = F.Id("H");
        var qg = F.Id("qG");
        var qh = F.Id("qH");
        var qu = F.Id("qU");
        var qi = F.Id("qI");
        var union = Call("SemilatticeSup.sup", g, h);
        var intersection = Call("SemilatticeInf.inf", g, h);
        var inequality = AtMost(Add(qu, qi), Add(qg, qh));
        var hypotheses = Imp(Call("IsSpectralDegreeExponent", g, qg),
            Imp(Call("IsSpectralDegreeExponent", h, qh),
                Imp(Call("IsSpectralDegreeExponent", union, qu),
                    Imp(Call("IsSpectralDegreeExponent", intersection, qi), inequality))));
        var exponents = All("qG", Reals(), All("qH", Reals(),
            All("qU", Reals(), All("qI", Reals(), hypotheses))));
        return All("n", Naturals(), All("G", GraphType(), All("H", GraphType(), exponents)));
    }

    private static Formula GraphBinders(Formula body) =>
        All("n", Naturals(), All("G", GraphType(), body));
    private static Formula Qualified(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. arguments]);
    private static Formula GraphType() => Call("SimpleGraph", Call("Fin", F.Id("n")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
