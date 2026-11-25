using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicGrowingThresholdExactDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicGrowingThresholdExact";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact finite score resolves every adjacent support decision at a leading rear threshold.",
        H("Exact support at a rear threshold"),
        Blocks(
            Paragraph(Text(
                "Fix parity e in {0,1}, index l≥0, a critical-scale sequence n⁵h(n)²→K, " +
                "adjacent rear offset sets S=S_l and T=S_(l+1), and shared boundary radius R=l+1+e/2. " +
                "Let p_S and p_T be the signed weights computed from the two three-moment fits.")),
            Describe.Lean(DescribeId.Create("adjacent-score"),
                DeclarationHandle.Create(Owner + ".adjacent_fit_score"),
                H("The two boundary scores have a positive determinant ratio"),
                StatementSource.FromAuthor(Comparison()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The larger window adds two distinct sites with offsets ±R. Their features coincide, " +
                    "so the assembled matrix changes by a rank-one outer product with multiplicity two. " +
                    "Subtract the exact fitted equations with common moment target and apply the matrix " +
                    "determinant lemma to identify the score ratio. Both determinants are eventually " +
                    "positive, since each tends to 16 times its window cardinality divided by 45. " +
                    "The identity also holds at a zero score."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-threshold-support"),
                DeclarationHandle.Create(Owner + ".eventual_support_at_leading_threshold"),
                H("The finite score determines the exact support"),
                StatementSource.FromAuthor(Selection()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume positive integer periods q(n) of eventual parity e, h(n)=2π/q(n), " +
                        "and Q=3K/20=T_e(l+1). For every sufficiently large n choose k=l+1 if " +
                        "p_S(R)>0, and k=l if p_S(R)≤0. This allows k to vary with n. " +
                        "The other rear endpoints and the front endpoints have strict leading signs.")),
                    Paragraph(Text(
                        "The finite optimizer certificate applies with a nonpositive omitted boundary, " +
                        "so equality of the score selects the smaller positive support. The fitted law is " +
                        "feasible with both exact cosine moment floors, is the unique minimum and has the " +
                        "squared-distance energy inequality. The support is the growing front and the selected " +
                        "rear window, for arbitrary approach rates to the leading critical scale."))),
                DescribeRole.Theorem))));

    private static Formula Comparison()
    {
        var s = F.Id("S");
        var t = F.Id("T");
        var r = F.Id("R");
        return F.Disp(Eq(Mul(Call("Det", Call("MomentMatrix", s)), Call("SignedValue", s, r)),
            Mul(Call("Det", Call("MomentMatrix", t)), Call("SignedValue", t, r))));
    }

    private static Formula Selection()
    {
        var score = Call("SignedValue", F.Id("S"), F.Id("R"));
        var l = F.Id("l");
        var k = F.Id("k");
        var positive = new Formula.Logic(
            new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, score),
            FormulaLogicOperator.Implies, Eq(k, new Formula.Binary(l, FormulaBinaryOperator.Add, F.D(1))));
        var nonpositive = new Formula.Logic(
            new Formula.Relation(score, FormulaRelationOperator.LessThanOrEqual, F.D(0)),
            FormulaLogicOperator.Implies, Eq(k, l));
        return F.Disp(new Formula.Logic(positive, FormulaLogicOperator.And, nonpositive));
    }

    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
