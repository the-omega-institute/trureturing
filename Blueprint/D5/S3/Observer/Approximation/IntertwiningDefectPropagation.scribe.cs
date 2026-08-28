using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Approximation;

internal sealed class IntertwiningDefectPropagationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Approximation/IntertwiningDefectPropagation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An operator intertwining defect telescopes and propagates with exact norm bounds.",
        H("Intertwining Defect Propagation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("intertwining-defect-telescope"),
                DeclarationHandle.Create(Prefix + "intertwining_defect_telescope"),
                H("Intertwining defects telescope exactly"),
                StatementSource.FromAuthor(TelescopeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let T and A be continuous linear endomorphisms of possibly distinct "
                            + "spaces, and let C map the source space to the target. The time-n "
                            + "defect is the sum of the one-step defect transported by the "
                            + "remaining powers of A and the elapsed powers of T.")),
                    Paragraph(Text(
                        "A noncommutative-ring induction proves exact cancellation. At time "
                            + "zero the finite sum is empty and both sides are zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("norm-intertwining-defect-bound"),
                DeclarationHandle.Create(Prefix + "norm_intertwining_defect_le"),
                H("The propagated defect has a weighted norm bound"),
                StatementSource.FromAuthor(NormBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The triangle inequality, the operator-norm composition bound, and "
                            + "the norm bound for powers turn the exact telescope into the "
                            + "finite weighted sum stated in the source corollary.")),
                    Paragraph(Text(
                        "No finite-dimensional, completeness, inner-product, or nontrivial "
                            + "carrier assumption is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-norm-intertwining-defect-bound"),
                DeclarationHandle.Create(Prefix + "uniform_norm_intertwining_defect_le"),
                H("Uniform norm bounds give linear propagation"),
                StatementSource.FromAuthor(UniformBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If both operator norms are at most L, every summand is at most "
                            + "L to the power n minus one times the one-step defect norm. "
                            + "There are exactly n summands.")),
                    Paragraph(Text(
                        "The proof does not need L less than one. Natural subtraction is "
                            + "truncated, so at n equal to zero its exponent is zero while "
                            + "the leading factor n makes the right side zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("left-norm-bound-is-necessary"),
                DeclarationHandle.Create(Prefix + "left_norm_bound_is_necessary"),
                H("The bound on A is necessary"),
                StatementSource.FromAuthor(LeftCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the one-dimensional real space take A as multiplication by two, "
                            + "C as the identity, T as zero, L as one, and n as three. The "
                            + "bound on T holds, but the claimed conclusion without the bound "
                            + "on A is false."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-norm-bound-is-necessary"),
                DeclarationHandle.Create(Prefix + "right_norm_bound_is_necessary"),
                H("The bound on T is necessary"),
                StatementSource.FromAuthor(RightCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The symmetric one-dimensional counterexample takes A as zero, C as "
                            + "the identity, T as multiplication by two, L as one, and n as "
                            + "three. The bound on A holds, but the conclusion without the "
                            + "bound on T is false."))),
                DescribeRole.Theorem))));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula NormOf(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert);

    private static Formula Defect(Formula a, Formula c, Formula t) =>
        Subtract(Multiply(c, t), Multiply(a, c));

    private static Formula IteratedDefect(
        Formula a,
        Formula c,
        Formula t,
        Formula n) =>
        Subtract(Multiply(c, Power(t, n)), Multiply(Power(a, n), c));

    private static Formula WeightedTerm(
        Formula a,
        Formula c,
        Formula t,
        Formula n,
        Formula j,
        bool withNorms)
    {
        Formula left = withNorms ? NormOf(a) : a;
        Formula middle = withNorms ? NormOf(Defect(a, c, t)) : Defect(a, c, t);
        Formula right = withNorms ? NormOf(t) : t;
        Formula leftPower = Power(left, Seq(n, Minus, D(1), Minus, j));
        return Multiply(Multiply(leftPower, middle), Power(right, j));
    }

    private static Formula FiniteSum(Formula term, Formula n, Formula j) =>
        Seq(
            Sum, Underscore, Grp(Seq(j, Eq, D(0))), Caret,
            Grp(Seq(n, Minus, D(1))), Sp, term);

    private static Formula UniformConclusion(
        Formula a,
        Formula c,
        Formula t,
        Formula l,
        Formula n) =>
        Seq(
            NormOf(IteratedDefect(a, c, t, n)), Sp, Leq, Sp,
            Multiply(
                Multiply(n, Power(l, Seq(n, Minus, D(1)))),
                NormOf(Defect(a, c, t))));

    private static Formula TelescopeFormula()
    {
        Formula scalar = F.Id("k");
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula a = F.Id("A");
        Formula c = F.Id("C");
        Formula t = F.Id("T");
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        Formula sum = FiniteSum(WeightedTerm(a, c, t, n, j, false), n, j);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, source, Comma, Sp, target, Colon, Sp, type,
            Comma, Sp, OpenBracket, Call("NontriviallyNormedField", scalar), CloseBracket,
            Comma, Sp, OpenBracket, Call("SeminormedAddCommGroup", source), CloseBracket,
            Comma, Sp, OpenBracket, Call("NormedSpace", scalar, source), CloseBracket,
            Comma, Sp, OpenBracket, Call("SeminormedAddCommGroup", target), CloseBracket,
            Comma, Sp, OpenBracket, Call("NormedSpace", scalar, target), CloseBracket,
            Comma, RowBreak, Grp(),
            a, Colon, Sp, Call("ContinuousLinearMap", scalar, target, target), Comma, Sp,
            c, Colon, Sp, Call("ContinuousLinearMap", scalar, source, target), Comma, Sp,
            t, Colon, Sp, Call("ContinuousLinearMap", scalar, source, source), Comma, Sp,
            n, Colon, Sp, F.Id("Nat"), Comma, RowBreak, Grp(),
            Equal(IteratedDefect(a, c, t, n), sum)));
    }

    private static Formula NormBoundFormula()
    {
        Formula a = F.Id("A");
        Formula c = F.Id("C");
        Formula t = F.Id("T");
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        Formula sum = FiniteSum(WeightedTerm(a, c, t, n, j, true), n, j);
        return Disp(Seq(NormOf(IteratedDefect(a, c, t, n)), Sp, Leq, Sp, sum));
    }

    private static Formula UniformBoundFormula()
    {
        Formula a = F.Id("A");
        Formula c = F.Id("C");
        Formula t = F.Id("T");
        Formula l = F.Id("L");
        Formula n = F.Id("n");
        Formula assumptions = Seq(
            NormOf(a), Sp, Leq, Sp, l, Sp, Land, Sp,
            NormOf(t), Sp, Leq, Sp, l);
        return Disp(Seq(
            assumptions, Sp, Rightarrow, Sp, UniformConclusion(a, c, t, l, n)));
    }

    private static Formula LeftCounterexampleFormula()
    {
        Formula a = D(2);
        Formula c = D(1);
        Formula t = D(0);
        Formula l = D(1);
        Formula n = D(3);
        return Disp(Seq(
            NormOf(t), Sp, Leq, Sp, l, Sp, Land, Sp,
            Neg, UniformConclusion(a, c, t, l, n)));
    }

    private static Formula RightCounterexampleFormula()
    {
        Formula a = D(0);
        Formula c = D(1);
        Formula t = D(2);
        Formula l = D(1);
        Formula n = D(3);
        return Disp(Seq(
            NormOf(a), Sp, Leq, Sp, l, Sp, Land, Sp,
            Neg, UniformConclusion(a, c, t, l, n)));
    }
}
