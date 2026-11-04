using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ConferenceGraphSedentarinessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/godsil2021sedentary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conference walks have sharp square-order floors and nonsquare vanishing infima.",
        H("Sharp return probabilities for conference graphs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The square-order classification and the family bound"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For m at least one, a conference graph has strongly regular parameters "
                    + "(4m + 1, 2m, m − 1, m). Its order is n = 4m + 1. At each vertex, the squared "
                    + "norm of the diagonal walk entry has sharp lower bound 1/n² at square orders, "
                    + "with equality at a positive time. At nonsquare orders it is nonnegative "
                    + "and becomes smaller than every positive real number at a positive time. "
                    + "For each c > 0, all sufficiently large conference graphs have, at every vertex, "
                    + "a positive time with return probability below c. The time may depend on the vertex. "
                    + "The walk is hamiltonianPropagator applied at −t, hence exp(itA). "
                    + "Godsil defines U(t) and M(t) in the arXiv v1 TeX source conemix.tex, "
                    + "lines 190–207, and asks "
                    + "whether conference-graph diagonal entries of M(t) can be bounded away from zero "
                    + "at lines 1035–1038. The classification here answers that question; the source "
                    + "does not state this classification as a theorem. No existence of conference "
                    + "graphs at prescribed orders is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Sharp square-order floors and vanishing nonsquare infima"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix m ≥ 1 and a graph with the stated strongly regular parameters. "
                        + "Write n = 4m + 1, A for its complex adjacency matrix, I for the identity "
                        + "matrix and J for the all-ones matrix. The common-neighbor counts give "
                        + "A² = 2mI + (m − 1)A + m(J − I − A) = mI − A + mJ. "
                        + "Regularity gives AJ = JA = 2mJ, and the vertex count is n.")),
                    Paragraph(Text(
                        "Set r = √n, θ = (−1 + r)/2, τ = (−1 − r)/2, P = J/n, Q = I − P "
                        + "and B = A − 2mP. The constant projection is idempotent. The identities "
                        + "BP = PB = 0, Q² = Q, BQ = QB = B and B² + B = mQ follow. "
                        + "Since θ + τ = −1, θ − τ = r and θτ = −m, the matrices "
                        + "E = (B − τQ)/r and F = (θQ − B)/r satisfy BE = θE and BF = τF. "
                        + "Consequently P, E and F are pairwise orthogonal idempotents, "
                        + "P + E + F = I and A = 2mP + θE + τF. At every vertex u, "
                        + "Pᵤᵤ = 1/n and Eᵤᵤ = Fᵤᵤ = 2m/n: these follow from "
                        + "Aᵤᵤ = 0, Bᵤᵤ = −2m/n and Qᵤᵤ = (n − 1)/n.")),
                    Paragraph(Text(
                        "The three scalar multiples of the idempotents commute. Factoring the "
                        + "exponential of their sum and using exp(zP) = I + (exp(z) − 1)P "
                        + "gives exp(aP + bE + cF) = exp(a)P + exp(b)E + exp(c)F. "
                        + "Apply this with a = 2mit, b = iθt and c = iτt. Taking diagonal "
                        + "entries yields U(t)ᵤᵤ = exp(2mit)/n + (exp(iθt) + exp(iτt))2m/n. "
                        + "Extracting the unit phase exp(−it/2) and combining the last two "
                        + "exponentials as a cosine gives "
                        + "pᵤ(t) = |exp(int/2) + (n − 1)cos(rt/2)|²/n².")),
                    Paragraph(Text(
                        "If n = q² for a natural q, then q is odd and q ≥ 3. The inequality "
                        + "|sin(qx)| ≤ q|sin x|, applied at x + π/2, gives "
                        + "|cos(qx)| ≤ q|cos x|. Put x = qt/2 and a = n − 1. Expanding the "
                        + "squared norm gives n²pᵤ(t) = 1 + a²cos²x + 2a cos x cos(qx). "
                        + "The absolute-value bound on the mixed product and a − 2q ≥ 0 "
                        + "give n²pᵤ(t) ≥ 1 + a(a − 2q)cos²x ≥ 1. "
                        + "For every order, t = π/√n is positive and makes cos(rt/2) zero, "
                        + "so pᵤ(t) = 1/n². In particular t = π/q attains the square-order bound.")),
                    Paragraph(Text(
                        "If n is nonsquare, r = √n is irrational, and therefore the integer "
                        + "multiples of the angle 2π/r are dense in the circle. On that circle "
                        + "the continuous function f(z) = (1 + 4m cos z)²/n² vanishes at "
                        + "z = arccos(−1/(4m)) and satisfies f(0) = 1. For every ε > 0, "
                        + "density supplies an integer j with f(j·2π/r) < min(ε, 1). "
                        + "This j is nonzero. Choose t = 4π|j|/n > 0. Then exp(int/2) = 1, "
                        + "rt/2 = |j|·2π/r, and evenness of cosine identifies the return "
                        + "probability with f(j·2π/r), which is below ε. Squared norms are "
                        + "nonnegative, proving that the infimum over positive times is zero.")),
                    Paragraph(Text(
                        "Finally fix c > 0 and choose a natural N with N > max(1, 1/c). "
                        + "For every order n ≥ N, the positive time π/√n has return "
                        + "probability 1/n² < c. This proves the family clause directly "
                        + "from the attained value, for both square and nonsquare orders."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("godsil-2017-conference-graph-sedentariness"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimBody()
    {
        var squareCase = Arrow(At(Qualified("IsSquare"), Order()), And(
            All("t", Reals(), LE(Floor(), Probability())),
            Some("t", Reals(), And(LT(D(0), X("t")), Equal(Probability(), Floor())))));
        var nonsquareCase = Arrow(new Formula.Not(Parenthesized(At(Qualified("IsSquare"), Order()))), And(
            All("t", Reals(), LE(D(0), Probability())),
            All("ε", Reals(), Arrow(LT(D(0), X("ε")),
                Some("t", Reals(), And(LT(D(0), X("t")), LT(Probability(), X("ε"))))))));
        var classification = All("m", Naturals(), Arrow(LE(D(1), X("m")),
            GraphBinders(All("u", X("V"), And(squareCase, nonsquareCase)))));
        var smallReturn = Some("t", Reals(), And(LT(D(0), X("t")), LT(Probability(), X("c"))));
        var familyGraphs = GraphBinders(All("u", X("V"), smallReturn));
        var family = All("c", Reals(), Arrow(LT(D(0), X("c")), Some("N", Naturals(),
            All("m", Naturals(), Arrow(LE(D(1), X("m")), Arrow(LE(X("N"), Order()), familyGraphs))))));
        return And(classification, family);
    }

    private static Formula GraphBinders(Formula body) => All("V", Qualified("Type"),
        InstanceBinder(At(Qualified("Fintype"), X("V")),
            InstanceBinder(At(Qualified("DecidableEq"), X("V")),
                All("G", At(Qualified("SimpleGraph"), X("V")),
                    InstanceBinder(At(Qualified("DecidableRel"), At(Qualified("SimpleGraph", "Adj"), X("G"))),
                        Arrow(At(Qualified("SimpleGraph", "IsSRGWith"), X("G"), Order(),
                            Multiply(D(2), X("m")), Subtract(X("m"), D(1)), X("m")), body))))));

    private static Formula Order() => Add(Multiply(D(4), X("m")), D(1));
    private static Formula RealOrder() => Add(Multiply(D(4),
        Typed(At(Qualified("Nat", "cast"), X("m")), Reals())), D(1));
    private static Formula Floor() => new Formula.Fraction(D(1), new Formula.Power(Parenthesized(RealOrder()), D(2)));
    private static Formula Probability() => new Formula.Power(new Formula.Norm(
        At(Qualified("D5", "S3", "Quantum", "Dynamics", "ProjectionProbabilityFlow", "hamiltonianPropagator"),
            At(Qualified("SimpleGraph", "adjMatrix"), Complexes(), X("G")),
            new Formula.Negate(X("t")), X("u"), X("u"))), D(2));

    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Dynamics", "ConferenceGraphSedentariness", name);
    private static Formula X(string name) => name == "ε" ? Varepsilon : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula InstanceBinder(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
