using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class LatticeConvolutionVarianceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/LatticeConvolutionVariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A global cosine minorant and lattice-period averaging bound the collision mass of degree sums.",
        H("Lattice convolution and variance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("score-variance-lower"),
                DeclarationHandle.Create(Owner + ".score_variance_lower"),
                H("A pointwise lower bound for the score norm"),
                StatementSource.FromAuthor(Score()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J be a finite type, g and w real functions on J, a and V real, and "
                        + "t any real time. Write W=Σ w(j), B=Σ w(j)(g(j)−a)², "
                        + "and S(t)=Σ w(j) exp(i g(j)t), all sums over J. "
                        + "The weights are nonnegative and the moment budget is B≤VW.")),
                    Paragraph(Text(
                        "Subtracting a from each frequency rotates the score by a unit phase. "
                        + "Its centered real part is Σ w(j) cos((g(j)−a)t). "
                        + "Use the global cosine bound cos(x)≥1−x²/2, multiply by the "
                        + "nonnegative weights, and insert the moment budget. The norm dominates "
                        + "both the real part and zero. If B>0 and t is nonzero, at least one positive-weight term has nonzero centered argument. Its cosine inequality is strict, which makes the unclipped actual-moment minorant strictly smaller than the norm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lattice-period-collision"),
                DeclarationHandle.Create(Owner + ".lattice_period_collision"),
                H("Exact averaging over a lattice period"),
                StatementSource.FromAuthor(Period()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J be finite with decidable equality, a(j) integers, w(j) real weights "
                        + "of either sign, b real, h>0 and g(j)=b+h a(j). For natural degree p, let E be "
                        + "tailCollisionMass g w p η. For any positive natural k and real s, set A=kπ/h and define Q(p,k,s) as the mean of "
                        + "|S(t)|^(2p) over [s−A,s+A], with S the complex score for g and w.")),
                    Paragraph(Text(
                        "The exact expansion in "),
                        Ref("D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.moment_eq_pair"),
                        Text(" writes the score power as the finite cosine pair sum of the monomial "
                            + "frequencies. Each such frequency is pb plus h times an integer. "
                            + "The common pb cancels in every difference. The mean of the remaining "
                            + "cosine is cos(hds) sinc(kπd) for an integer d, equal to one at d=0 and zero "
                            + "elsewhere. For 0≤η<h the closed collision band retains these same pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lattice-collision-variance-lower"),
                DeclarationHandle.Create(Owner + ".lattice_collision_variance_lower"),
                H("Finite collision lower bound for lattice convolutions"),
                StatementSource.FromAuthor(Collision()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the affine lattice frequencies and notation of the preceding statement, "
                        + "now with w(j)≥0, arbitrary real center a, and B=Σ w(j)(g(j)−a)²≤VW "
                        + "where W=Σ w(j). Set A=π/h. Let R(p,V,A) be the mean over [−A,A] of "
                        + "max(0,1−Vt²/2)^(2p). The resolution η is nonnegative.")),
                    Paragraph(Text(
                        "Raise the pointwise score bound to the even natural power 2p, "
                        + "then integrate over a full lattice period. Since the pair weights are nonnegative, "
                        + "increasing the closed-band radius from zero to η can only increase collision mass. "
                        + "The finite integral retains the contribution of the convolution structure. "
                        + "At zero variance budget it gives the full mass W^(2p). If B>0 and p>0, choose a sufficiently small positive time inside the averaging interval. The pointwise strict inequality and continuity make the integrated comparison strict.")),
                    Paragraph(Text(
                        "The integral can be rescaled by √(pV) when p and V are positive. Its limiting Gaussian "
                        + "coefficient is a separate asymptotic problem. Extending the full-period argument "
                        + "to general real frequency differences requires a kernel accounting for the closed "
                        + "band; the lattice hypothesis supplies exact orthogonality here."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula NonnegativeWeights()
    {
        var j = F.Id("j");
        return Seq(Forall, Sp, j, InMacro, Sp, F.Id("J"), Comma, Sp,
            D(0), Leq, Sp, Call("w", j));
    }

    private static Formula Budget() => Seq(F.Id("B"), Leq, Sp, Multiply(F.Id("V"), F.Id("W")));

    private static Formula Score()
    {
        var t = F.Id("t");
        var assumptions = Seq(NonnegativeWeights(), Quad, Sp, Budget());
        var rhs = Seq(Lvert, Call("S", t), Rvert);
        var margin = Call("max", D(0), Subtract(D(1),
            new Formula.Fraction(Multiply(F.Id("V"), new Formula.Power(t, D(2))), D(2))));
        var w = F.Id("W");
        var b = F.Id("B");
        var actual = Subtract(w, new Formula.Fraction(Multiply(b, new Formula.Power(t, D(2))), D(2)));
        var first = new Formula.Relation(Multiply(w, margin), FormulaRelationOperator.LessThanOrEqual, rhs);
        var second = new Formula.Relation(Call("max", D(0), actual), FormulaRelationOperator.LessThanOrEqual, rhs);
        var strict = new Formula.Logic(Seq(D(0), Lt, Sp, b, Comma, Sp, t, Neq, Sp, D(0)),
            FormulaLogicOperator.Implies, new Formula.Relation(actual, FormulaRelationOperator.LessThan, rhs));
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
            Seq(first, Comma, Sp, second, Comma, Sp, Open, strict, Close)));
    }

    private static Formula Period()
    {
        var h = F.Id("h");
        var eta = F.Id("eta");
        var assumptions = Seq(D(0), Lt, Sp, h, Comma, Sp, D(0), Leq, Sp, eta, Lt, Sp, h,
            Comma, Sp, D(0), Lt, Sp, F.Id("k"));
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
            Equal(Call("Q", F.Id("p"), F.Id("k"), F.Id("s")), F.Id("E"))));
    }

    private static Formula Collision()
    {
        var p = F.Id("p");
        var assumptions = Seq(NonnegativeWeights(), Quad, Sp, Budget(), Comma, Sp,
            D(0), Lt, Sp, F.Id("h"), Comma, Sp, D(0), Leq, Sp, F.Id("eta"));
        var lhs = Multiply(new Formula.Power(F.Id("W"), Multiply(D(2), p)),
            Call("R", p, F.Id("V"), F.Id("A")));
        var weak = new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, F.Id("E"));
        var strict = new Formula.Logic(Seq(D(0), Lt, Sp, F.Id("B"), Comma, Sp, D(0), Lt, Sp, p),
            FormulaLogicOperator.Implies, new Formula.Relation(lhs, FormulaRelationOperator.LessThan, F.Id("E")));
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
            Seq(weak, Comma, Sp, Open, strict, Close)));
    }
}
