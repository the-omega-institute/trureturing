using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.TraceFibers;

internal sealed class FixedFiberPairModulusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One selected continuation has exact scalar and matrix moduli on the entire "
            + "positive rank-one source fiber of its fixed executed history.",
        H("Fixed Fiber Pair Modulus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upper-shear-power"),
                DeclarationHandle.Create("D5/S3/Observer/TraceFibers/FixedFiberPairModulus.upper_shear_power"),
                H("Upper shear powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/mathlib2026shearpowers")),
                Blocks(Paragraph(Text(
                    "The kth power of JM has rows (1,k) and (0,1), including the identity at k=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-shear-power"),
                DeclarationHandle.Create("D5/S3/Observer/TraceFibers/FixedFiberPairModulus.lower_shear_power"),
                H("Lower shear powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/mathlib2026shearpowers")),
                Blocks(Paragraph(Text(
                    "The kth power of MJ has rows (1,0) and (k,1), the transpose of the upper shear power."))),
                DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("fixed-fiber-pair-modulus"),
            DeclarationHandle.Create("D5/S3/Observer/TraceFibers/FixedFiberPairModulus.result"),
            H("Exact moduli from a common source pair"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The permitted atomic matrices are M with rows (0,1),(1,1), and J "
                        + "with rows (0,1),(1,0). A word lists operations chronologically, "
                        + "so its later operations multiply on the left. Fix the entire "
                        + "executed prefix, whose endpoint is U^k or V^k with U=JM, "
                        + "V=MJ and k at least one. The initial identity read counts; "
                        + "there are three reads and the total action count is the "
                        + "prefix length plus the selected continuation length.")),
                Paragraph(Text(
                    "For positive x and zeta, positive rank-one sources with initial "
                        + "read x and second read x+k*zeta are exactly R(s), 0<s<x. "
                        + "The upper fiber has rows (x-s,s*(x-s)/zeta),(zeta,s); the "
                        + "lower fiber has rows (x-s,zeta),(s*(x-s)/zeta,s). Every "
                        + "positive rank-one source factors as a positive column times "
                        + "a positive fixed measurement row. Every cumulative read is "
                        + "the fixed row applied to the transformed column.")),
                Paragraph(Text(
                    "Select one legal continuation before its third read, and set B "
                        + "to its matrix times the prefix matrix. On the upper fiber "
                        + "e=B21; on the lower fiber e=B12. Put D=B22-B11, alpha=e/zeta "
                        + "and mu=abs(D)-alpha*x. Assume e>0 and mu>=0, retaining both "
                        + "signs of D and the equality case mu=0.")),
                Paragraph(Text(
                    "Both suprema use exactly the same pairs u,v in (0,x) whose "
                        + "raw third trace readings differ by at most tau. Equal pairs "
                        + "are allowed. Scalar distance is abs(u-v), and matrix "
                        + "distance is the maximum absolute entry among all four "
                        + "entries of R(u)-R(v). Neither supremum is defined by its "
                        + "closed formula.")),
                Paragraph(Text(
                    "Writing l=abs(u-v) and z=x-u-v gives readout distance "
                        + "l*abs(D+alpha*z) and matrix distance max(l,l*abs(z)/zeta). "
                        + "An unequal interior pair has abs(z)<x-l, so its readout "
                        + "distance strictly exceeds mu*l+alpha*l^2. This bounds "
                        + "spacing by the clipped root and the matrix objective by "
                        + "the geometric envelope.")),
                Paragraph(Text(
                    "For each positive spacing below the clipped root and each "
                        + "threshold below l*(x-l)/zeta, a single interior pair "
                        + "simultaneously satisfies the readout constraint and exceeds "
                        + "the objective threshold. A positive endpoint displacement "
                        + "is chosen to preserve the domain, readout slack and matrix "
                        + "margin. Reflecting the pair handles the other sign of D. "
                        + "These common pairs supply both supremum lower bounds, "
                        + "including the capped root and its boundary.")),
                Paragraph(Text(
                    "For positive tolerance both suprema are positive and every "
                        + "feasible interior pair lies strictly below them. At zero "
                        + "tolerance both are zero and the equal pair s=x/2 attains "
                        + "them. All sources and reads belong to the same executed "
                        + "history and chosen continuation; the model introduces "
                        + "no reset, copy, inverse operation or unexecuted branch."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula x = F.Id("x");
        Formula zeta = Zeta;
        Formula tau = Tau;
        Formula alpha = Alpha;
        Formula mu = Mu;
        Formula w = F.Id("w");
        Formula b = F.Id("b");
        Formula omega = Call(new Formula.Subscript(
            Seq(Operatorname, Grp(F.Id("Omega"))), F.Id("B")), tau);
        Formula matrix = Call(new Formula.Subscript(
            Seq(Mathcal, Grp(F.Id("M"))), F.Id("B")), tau);
        Formula root = Seq(Sqrt, Grp(new Formula.Power(mu, D(2)), Plus,
            D(4), Cdot, alpha, Cdot, tau));
        Formula r = new Formula.Fraction(Seq(root, Minus, mu), Seq(D(2), Cdot, alpha));
        Formula geometric = Call("max", w,
            new Formula.Fraction(Seq(b, Cdot, Grp(Seq(x, Minus, b))), zeta));
        return Disp(new Formula.Aligned([
            Seq(x, Sp, Gt, Sp, D(0), Comma, Sp, zeta, Sp, Gt, Sp, D(0), Comma,
                Sp, tau, Sp, Ge, Sp, D(0), Comma, Sp, F.Id("e"), Sp, Gt, Sp, D(0)),
            Seq(alpha, Sp, Eq, Sp, new Formula.Fraction(F.Id("e"), zeta), Comma,
                Sp, mu, Sp, Eq, Sp, Seq(Call("abs", F.Id("D")), Minus, alpha, Cdot, Sp, x),
                Sp, Ge, Sp, D(0)),
            Seq(w, Sp, Eq, Sp, Call("min", x, r), Comma, Sp, b, Sp, Eq, Sp,
                Call("min", w, new Formula.Fraction(x, D(2)))),
            Seq(omega, Sp, Eq, Sp, w, Comma, Sp, matrix, Sp, Eq, Sp, geometric),
            Seq(tau, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                Call(Seq(F.Text, Grp(F.Id("positive"), Sp, F.Id("unattained"))),
                    omega, matrix)),
            Seq(tau, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp, omega, Sp, Eq, Sp,
                matrix, Sp, Eq, Sp, D(0), Comma, Sp,
                Call(Seq(F.Text, Grp(F.Id("attained"), Sp, F.Id("at"), Sp,
                    F.Id("equal"), Sp, F.Id("pair"))), new Formula.Fraction(x, D(2))))
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
        => Call(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var pieces = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
