using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class GeometricTraceConvexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint convexity of Hiai's original CFC geometric trace on supported PSD pairs.",
        H("GeometricTraceConvexity"), Blocks(
            Describe.Lean(DescribeId.Create("geometric-trace-joint-convexity"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricTraceConvexity.geometric_trace_jointly_convex"),
                H("The boundary-inclusive SPD rectangle"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/hiai2025geometrictraceconvexity")),
                Blocks(Paragraph(Text("For every finite complex matrix index type d with "
                    + "DecidableEq, including empty d, and every 1 <= alpha <= 2 and "
                    + "1/2 <= p <= 1, the function F(A,B)=Re Tr((A to exponent p "
                    + "geometricMean at weight alpha B to exponent p) to exponent 1/p) "
                    + "is jointly convex on the two positive definite cones. The base "
                    + "is A to exponent p, the FIRST matrix argument. All powers are "
                    + "actual CFC spectral powers. A and B need not commute.")),
                    Paragraph(Text("Set theta=alpha-1, r=1/p, X=B to exponent p and "
                    + "M=geometricMean theta (B to exponent p) (A to exponent p). "
                    + "The existing all-real weighted symmetry and inverse sandwich "
                    + "identify the original mean with X inverse(M) X. Public matrix "
                    + "unit-congruence positivity and spectral strictness make M "
                    + "positive definite. Matrix nonsingular inverse agrees with "
                    + "Ring.inverse. The existing inverse variational theorem gives "
                    + "the invertible optimizer inverse(M) X, not necessarily selfadjoint, "
                    + "with equality and an upper bound for EVERY Z.")),
                    Paragraph(Text("Since (B to exponent p) squared equals B to exponent "
                    + "2p, the objective is 2 C_Z(B)-Psi_Z(A,B), where "
                    + "C_Z(B)=Re Tr((Z adjoint B to exponent 2p Z) to exponent 1/(2p)). "
                    + "The existing Carlen-Lieb fixed-congruence theorem at a=2p "
                    + "makes C_Z convex; its first component also supplies SPD "
                    + "domain convexity. The existing Hiai Psi theorem makes Psi_Z "
                    + "jointly concave for this same fixed invertible Z.")),
                    Paragraph(Text("Choose ONLY the attained optimizer Zm at the mixed "
                    + "pair ((1-t)A0+tA1,(1-t)B0+tB1). Fixed-Zm objective convexity "
                    + "bounds F at this pair by the mixed endpoint objectives. Apply "
                    + "the universal variational upper bound at BOTH endpoints to "
                    + "that SAME Zm. Nonnegative weights then give joint convexity. "
                    + "No mixing of optimizers, uniqueness, compactness, assumed "
                    + "supremum attainment, A/B commutation, product positivity, "
                    + "or CFC transport through arbitrary congruence is used.")),
                    Paragraph(Text("The definition is Hiai (2.1)/(2.2), page 4 of "
                    + "arXiv:2510.04691v3; Problem 5.18 is on page 33. Classical "
                    + "Hiai, Carlen-Lieb, Zhang and the attributed Physlib suppliers "
                    + "retain their source credit. This is a connected formal "
                    + "assembly on SPD, with no novelty claim for reused theorems. "
                    + "It supplies the regularized original parameter rectangle on SPD and "
                    + "known parameter endpoints for the extension to the full "
                    + "support-sensitive PSD original domain below.")),
                    Paragraph(Text("The PSD endpoint below uses the same epsilon I added "
                    + "to both original matrices before their p-powers, the actual "
                    + "support spectral identity, and a trace limit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geometric-trace-support-convexity"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricTraceConvexity.geometric_trace_support_convex"),
                H("The original PSD support domain"), StatementSource.FromAuthor(SupportStatement()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/hiai2025geometrictraceconvexity")),
                Blocks(Paragraph(Text("For every finite complex carrier d, including the empty "
                    + "carrier, supportPairDomain consists exactly of pairs (A,B) with A and B "
                    + "positive semidefinite and ker A contained in ker B. The unchanged "
                    + "geometricTrace formula is ConvexOn over this coupled set of pairs "
                    + "for 1 <= alpha <= 2 and 1/2 <= p <= 1. The mean is the classical "
                    + "base-first quasi-geometric mean G of Hiai, with A to exponent p "
                    + "as its base. It is distinct from SG and tilde-SG.")),
                    Paragraph(Text("Fix a supported pair. Q=I-spectralSupport(A) is the "
                    + "kernel projection, and both A Q and B Q vanish. Finite-spectrum "
                    + "CFC gives the exact decomposition of (A+epsilon I) to exponent "
                    + "-p/2 into a support-restricted factor and epsilon to exponent "
                    + "-p/2 times Q. The inner sandwich is the supported sandwich plus "
                    + "Q, because the powered B regularization acts on Q as epsilon "
                    + "to exponent p. These use the actual curves (A+epsilon I) to "
                    + "exponent p and (B+epsilon I) to exponent p.")),
                    Paragraph(Text("The support-restricted negative powers converge on "
                    + "the fixed finite spectrum. Positive powers are continuous on PSD "
                    + "matrices. At the limit, finite spectral intertwining removes Q "
                    + "between the outer A to exponent p/2 factors. The resulting mean "
                    + "is exactly the original Moore-Penrose CFC formula, including "
                    + "A=B=0 and empty carriers. Positive 1/p power continuity and "
                    + "trace continuity give the required real trace limit.")),
                    Paragraph(Text("For an interior mixture, vanishing of a PSD quadratic "
                    + "form forces both endpoint A matrices to annihilate the vector. "
                    + "Their kernel inclusions then give annihilation by the mixed B. "
                    + "The t=0 and t=1 cases are separate. Adding the same epsilon I "
                    + "commutes exactly with mixing; apply the preserved SPD convexity "
                    + "theorem and pass the three trace limits through closed real order.")),
                    Paragraph(Text("The limit concerns simultaneous additive epsilon I "
                    + "regularization of a fixed supported pair. It asserts no continuity "
                    + "on the entire support domain and uses no singular ring inverse "
                    + "or reverse-base identity. The exact original-domain endpoint "
                    + "is the formal target of Hiai Problem 5.18."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Statement()
    {
        var d = F.Id("d"); var a = F.Id("alpha"); var p = F.Id("p");
        var x = F.Id("A"); var y = F.Id("B");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var matrix = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        var cone = Call("PosDefCone", matrix);
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Sp,
            d, Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            a, Comma, Sp, p, Colon, Sp, real, Comma, Esc,
            D(1), Le, Sp, a, Sp, Le, Sp, D(2), Land, Sp,
            new Formula.Fraction(D(1), D(2)), Le, Sp, p, Sp, Le, Sp, D(1), Implies, Esc,
            Call("JointlyConvexOn", cone, cone,
                Seq(Lambda, Sp, x, Comma, Sp, y, Mapsto,
                    Call("tracePower", new Formula.Fraction(D(1), p),
                        Call("geometricMean", a, Call("rpow", x, p), Call("rpow", y, p))))));
    }

    private static Formula SupportStatement()
    {
        var d = F.Id("d"); var a = F.Id("alpha"); var p = F.Id("p"); var z = F.Id("z");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Sp,
            d, Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            a, Comma, Sp, p, Colon, Sp, real, Comma, Esc,
            D(1), Le, Sp, a, Sp, Le, Sp, D(2), Land, Sp,
            new Formula.Fraction(D(1), D(2)), Le, Sp, p, Sp, Le, Sp, D(1), Implies, Esc,
            Call("ConvexOn", real, Call("supportPairDomain", d),
                Seq(Lambda, Sp, z, Mapsto,
                    Call("geometricTrace", a, p, Call("fst", z), Call("snd", z)))));
    }
}
