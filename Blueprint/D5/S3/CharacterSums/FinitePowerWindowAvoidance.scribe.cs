using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class FinitePowerWindowAvoidanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete power window avoiding finitely many real obstacles",
        H("Finite obstacles and an explicit lower endpoint"),
        Blocks(
            Paragraph(Text("Let E be any finite set of real numbers, X > 1 and L ≥ 1. "
                + "Require η > 0 only when η < C. "
                + "There is no positivity assumption on the obstacles, nor on C. Put "
                + "J = L if C ≤ η, and J = L(LC/η)^card(E0) otherwise, "
                + "where E0 = {a in E : 1 < a ≤ X^C}; loss(E,η,C,X,L) denotes this J. "
                + "The formula uses finite(E), admissible(η,C,X,L), and good(E,η,C,Y,L) "
                + "for these conditions and the full closed-window implication below.")),
            Describe.Lean(DescribeId.Create("finite-power-window"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/FinitePowerWindowAvoidance.finite_power_window"),
                H("Quantitative avoidance on a closed power window"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This repository derivation strengthens Alpöge's formalized "
                        + "UpperTheory.V.Win.window (V/LayeredIsomorphisms/Window.lean). At the "
                        + "pinned revision its file is src/Development/AutomorphicArithmetic/"
                        + "AutomorphicVarieties/LayeredIsomorphisms/Window.lean in "
                        + "https://github.com/the-omega-institute/riemann-hypothesis at commit "
                        + "c7d25b3bfd7906388bb8eb0774e027a2b756a7b6. It permits arbitrary real "
                        + "obstacles, any width L ≥ 1, and counts only effective obstacles.")),
                    Paragraph(Text("The conclusion is Y > 1, X^(1/J) ≤ Y, Y^L ≤ X, "
                        + "and for every real x in [Y,Y^L] and every a in E, "
                        + "a ≤ x^C implies a ≤ x^η. All endpoints are included.")),
                    Paragraph(Text("On logarithmic scale, for A ≥ 1, T > 0 and at most R "
                        + "thresholds, find s in [T/A^R,T] such that no threshold lies in "
                        + "(s,As]. If (T,AT] is empty, use s = T. Otherwise remove one "
                        + "threshold above T and recurse below T/A. The removed threshold "
                        + "lies strictly above every remaining forbidden interval. This "
                        + "proves the geometric gap by induction on the number of obstacles.")),
                    Paragraph(Text("For C > η use A = LC/η and T = η log(X)/L, "
                        + "apply the gap to logarithms of effective obstacles, and set "
                        + "Y = exp(s/η). Obstacles at most one satisfy the conclusion "
                        + "automatically; obstacles above X^C cannot occur. For C ≤ η use "
                        + "Y = X^(1/L); here J = L is optimal "
                        + "because Y^L ≤ X already forces Y ≤ X^(1/L).")),
                    Paragraph(Text("Taking L = 2 and E in the natural numbers gives "
                        + "J = 2^(card(E0)+1)(C/η)^card(E0) for C > η. If card(E) ≤ R and "
                        + "C/η ≥ 1, this implies the requested bound with "
                        + "J = 2^(R+2)(C/η)^R. It improves that loss by a factor of two "
                        + "when card(E0) = R, and improves further with fewer effective obstacles. "
                        + "Arbitrary real obstacles and widths, including L = 1, are included. "
                        + "The nontrivial "
                        + "constant is sharp uniformly over real obstacles: write "
                        + "A = LC/η and T = η log(X)/L. Choose b just above T and at most AT, "
                        + "and, for R ≥ 1, R obstacles with logarithms b/A^i, 0 ≤ i < R. Their "
                        + "forbidden intervals for s = η log(Y) cover [b/A^R,b). "
                        + "Thus no uniform improvement of the endpoint T/A^R is possible. "
                        + "For R = 0 sharpness follows directly from Y^L ≤ X.")),
                    Paragraph(Text("For a worst-case uniform guarantee based only on cardinality, "
                        + "a uniform bound on the effective obstacle count gives a fixed exponent "
                        + "loss. This is sufficient, not necessary: for E = {-1,...,-N}, "
                        + "the effective set is empty for every N and J = L. Even effective "
                        + "counts may grow while a fixed window works: with η = 1, C = L = 2, "
                        + "X = N^4, E = {1,...,N} and N ≥ 2, take Y = N^2 and J = 2."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var e = F.Id("E");
        var n = F.Id("eta");
        var c = F.Id("C");
        var x = F.Id("X");
        var l = F.Id("L");
        var y = F.Id("Y");
        var loss = At("loss", e, n, c, x, l);
        var conclusion = And(Lt(F.D(1), y),
            And(Le(At("power", x, At("inverse", loss)), y),
                And(Le(At("power", y, l), x), At("good", e, n, c, y, l))));
        return F.Disp(All("E", "FiniteRealSets", All("eta", "R", All("C", "R",
            All("X", "R", All("L", "R", Implies(At("admissible", n, c, x, l),
                Exists("Y", "R", conclusion))))))));
    }

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, string domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name), Sp(domain), body);
    private static Formula Exists(string name, string domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create(name), Sp(domain), body);
    private static Formula Sp(string name) => F.Seq(F.Mathbb, F.Sp, F.Grp(F.Id(name)));
}
