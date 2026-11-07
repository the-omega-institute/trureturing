using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GaussZeroBalanced;

internal sealed class FractionalLegendreTuranDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/GaussZeroBalanced/FractionalLegendreTuran.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karp2011sf21legendre");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational interior counterexample to Karp's fractional Legendre Turán inequality.",
        H("Fractional-degree Legendre Turán inequality"), Blocks(
            Describe.Lean(DescribeId.Create("karp-sf21-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 4"), StatementSource.FromAuthor(Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("Karp, SF21 slides, physical PDF p. 52 (also pp. 53–54), verbatim: “Curious open problems”; “Turán (1946) inequality for Legendre polynomials:”")),
                    Paragraph(Text("“₂F₁(−μ,1+μ;1;y)² > ₂F₁(−μ−δ,1+μ+δ;1;y)₂F₁(−μ+δ,1+μ−δ;1;y),”")),
                    Paragraph(Text("“for y∈(0,1), μ=1,2,… and δ=1.” “Conjecture 4” “Turán inequality is true for all μ>0 and 0<δ<1.”")),
                    Paragraph(Text("The real function gauss is the existing ordinaryHypergeometric over ℝ. The letters μ, δ and y are real numbers; the argument retains the open interval from the preceding display. The first product factor has degree μ+δ and the second degree μ−δ. No sign or zero-free restriction on the three values is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-sf21-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The fractional-degree assertion is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Take μ=3/2, δ=63/64 and y=4095/4096. The values at degrees 33/64, 96/64 and 159/64 lie respectively in [−23/10,−227/100], [181/100,184/100] and [−153/100,−150/100]. The central square is at most (184/100)², whereas the shifted product is at least (227/100)(150/100); their difference is strictly negative.")),
                    Paragraph(Text("The integer certificates enclose 10,000 recurrence steps at scale 10¹². Beyond a degree-dependent index the absolute term ratio is at most y, so the remaining series is bounded geometrically. All three degrees are positive. This strict interior counterexample also contradicts the non-strict comparison. Variants requiring positive function values or a zero-free range, and a uniform moving-shift family, remain open."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(Formula x, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(x, Colon, Sp, R)), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Negate(Formula x) => Seq(Minus, x);
    private static Formula G(Formula a, Formula b) => Call("gauss", a, b, D(1), F.Id("y"));
    private static Formula SourceDisplay() => new Formula.Relation(
        new Formula.Power(G(Negate(Mu), Add(D(1), Mu)), D(2)),
        FormulaRelationOperator.GreaterThan,
        Multiply(G(Subtract(Negate(Mu), DeltaLower), Add(Add(D(1), Mu), DeltaLower)),
            G(Add(Negate(Mu), DeltaLower), Subtract(Add(D(1), Mu), DeltaLower))));
    private static Formula ClaimBody() => All(Mu, All(DeltaLower, All(F.Id("y"),
        Imp(Lt(D(0), Mu), Imp(Lt(D(0), DeltaLower), Imp(Lt(DeltaLower, D(1)),
            Imp(Lt(D(0), F.Id("y")), Imp(Lt(F.Id("y"), D(1)), SourceDisplay()))))))));
}
