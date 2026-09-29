using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class ParityPathLikelihoodProductsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Against the uniform product reference on hypercube paths, same-direction parity-kernel path products "
            + "have inner product (1 + E[a b])^s and opposite-direction path products have inner product one; for "
            + "profiles with |a| < 1 these products are the path likelihood ratios.",
        H("Inner Products of Parity-Kernel Path Likelihoods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-path-likelihood"),
                DeclarationHandle.Create(Module + "forwardLikelihood"),
                H("Forward path product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub(F.Id("L"), Seq(F.Id("a"), Comma, Plus)), Open, F.Id("x"), Close, Eq, Sp,
                    Prod, Underscore, Grp(F.Id("t"), Lt, F.Id("s")), Sp,
                    D(2), Caret, Grp(F.Id("d")), Sp,
                    Sub(F.Id("P"), F.Id("a")), Open, Sub(F.Id("x"), F.Id("t")), Comma, Sp,
                    Sub(F.Id("x"), Seq(F.Id("t"), Plus, D(1))), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a path x_0, ..., x_s of sign vectors and a real profile a, the forward product of the parity kernel "
                        + "P_a is the product of 2^d P_a over the steps; for |a| < 1 it is the likelihood ratio of "
                        + "the forward path law against the uniform product reference."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("backward-path-likelihood"),
                DeclarationHandle.Create(Module + "backwardLikelihood"),
                H("Backward path product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub(F.Id("L"), Seq(F.Id("a"), Comma, Minus)), Open, F.Id("x"), Close, Eq, Sp,
                    Prod, Underscore, Grp(F.Id("t"), Lt, F.Id("s")), Sp,
                    D(2), Caret, Grp(F.Id("d")), Sp,
                    Sub(F.Id("P"), F.Id("a")), Open, Sub(F.Id("x"), Seq(F.Id("t"), Plus, D(1))), Comma, Sp,
                    Sub(F.Id("x"), F.Id("t")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The backward product uses every step in reverse; for |a| < 1 it is the likelihood ratio of the "
                        + "time-reversed path law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-path-mean"),
                DeclarationHandle.Create(Module + "uniformPathMean"),
                H("Uniform product reference"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub(F.Id("E"), F.Id("U")), OpenBracket, F.Id("F"), CloseBracket, Eq, Sp,
                    Open, Frac, Grp(D(1)), Grp(D(2), Caret, Grp(F.Id("d"))), Close, Caret,
                    Grp(F.Id("s"), Plus, D(1)), Sp,
                    Sum, Underscore, Grp(F.Id("x")), Sp, Call("F", F.Id("x"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reference law makes the s + 1 states of a path independent and uniform on the "
                        + "hypercube. When |a| < 1 the forward and backward products are the likelihood ratios of "
                        + "the forward and time-reversed path laws of P_a against this reference; the identities "
                        + "below are stated for every real profile."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-inner-product"),
                DeclarationHandle.Create(Module + "forward_inner_product"),
                H("Forward products: inner product"),
                StatementSource.FromAuthor(SameDirection(Plus)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If the profiles a and b both sum to zero over the hypercube, then for every number "
                            + "of steps s the forward products of P_a and P_b have uniform-reference inner "
                            + "product (1 + E[a b])^s, where E is the uniform average.")),
                    Paragraph(Text(
                        "The step matrix M(x, y) = 2^d P_a(x, y) 2^d P_b(x, y) equals 1 + chi(y)(a(x) + b(x)) "
                            + "+ a(x) b(x), because chi(y)^2 = 1. Hence every column of M sums to "
                            + "2^d (1 + E[a b]). Summing the edge products over all paths, the first state is "
                            + "summed out against a column, and induction on s gives 2^d times the s-th power of "
                            + "the column sum; the uniform normalization then leaves (1 + E[a b])^s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("backward-inner-product"),
                DeclarationHandle.Create(Module + "backward_inner_product"),
                H("Backward products: inner product"),
                StatementSource.FromAuthor(SameDirection(Minus)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same hypotheses the backward products have the same inner product. Now the "
                        + "reversed step matrix has constant row sums 2^d (1 + E[a b]), and the last state of "
                        + "the path is summed out at each induction step."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-backward-inner-product"),
                DeclarationHandle.Create(Module + "forward_backward_inner_product"),
                H("Opposite directions are orthogonal after centering"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("d"), Geq, Sp, D(1), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")), Sp, Call("b", F.Id("y")), Eq, D(0), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")), Sp, Call("chi", F.Id("y")), Sp, Call("b", F.Id("y")),
                    Eq, D(0), Sp, Rightarrow, Sp,
                    Sub(F.Id("E"), F.Id("U")), OpenBracket,
                    Sub(F.Id("L"), Seq(F.Id("a"), Comma, Plus)), Sp,
                    Sub(F.Id("L"), Seq(F.Id("b"), Comma, Minus)), CloseBracket, Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d >= 1. If the profile b sums to zero and chi b sums to zero, then for every "
                            + "profile a and every s the forward product of P_a and the backward product of "
                            + "P_b have inner product one. Each product has reference mean one, so the "
                            + "centered forward and backward products are orthogonal; for |a|, |b| < 1 these are the centered "
                            + "likelihood ratios of the two time directions.")),
                    Paragraph(Text(
                        "The step matrix H(x, y) = 2^d P_a(x, y) 2^d P_b(y, x) has row sums "
                            + "4^d (P_a P_b)(x, x) = 2^d: expanding the product, the parity sum vanishes (it is the record "
                            + "weight of the empty coordinate set) and the two remaining sums vanish by hypothesis. "
                            + "Summing out the last state at each step gives 2^d (2^d)^s, which the uniform "
                            + "normalization turns into one."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) result.AddRange([Comma, Sp]);
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula Sub(Formula name, Formula index) => Seq(name, Underscore, Grp(index));

    private static Formula SameDirection(Formula sign)
    {
        Formula a = F.Id("a"), b = F.Id("b");
        return Disp(Seq(
            Sum, Underscore, Grp(F.Id("y")), Sp, Call("a", F.Id("y")), Eq, D(0), Comma, Sp,
            Sum, Underscore, Grp(F.Id("y")), Sp, Call("b", F.Id("y")), Eq, D(0), Sp, Rightarrow, Sp,
            Sub(F.Id("E"), F.Id("U")), OpenBracket,
            Sub(F.Id("L"), Seq(a, Comma, sign)), Sp, Sub(F.Id("L"), Seq(b, Comma, sign)), CloseBracket, Eq, Sp,
            Open, D(1), Plus, Frac, Grp(D(1)), Grp(D(2), Caret, Grp(F.Id("d"))), Sp,
            Sum, Underscore, Grp(F.Id("y")), Sp, Call("a", F.Id("y")), Sp, Call("b", F.Id("y")), Close,
            Caret, Grp(F.Id("s"))));
    }
}
