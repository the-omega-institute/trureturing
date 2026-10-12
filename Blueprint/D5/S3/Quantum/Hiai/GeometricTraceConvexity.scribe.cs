using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class GeometricTraceConvexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint convexity of Hiai's original geometric trace on positive definite matrices.",
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
                    + "It covers the original open parameter rectangle on SPD and "
                    + "known parameter endpoints; it does not complete the full "
                    + "support-sensitive PSD original domain.")),
                    Paragraph(Text("The remaining original obligations are PSD "
                    + "support inclusion s(A)>=s(B), generalized inverse zero on "
                    + "kernels, the same epsilon I added to ORIGINAL A and B before "
                    + "their p-powers, a norm/trace limit, and support-domain "
                    + "convexity. Compression transport and block-support "
                    + "identities are not asserted. The native four-slot audit "
                    + "remains unfinished under issue #5214; no declared_validated "
                    + "registration or official acceptance is claimed."))), DescribeRole.Theorem))));

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
            D(1), Le, a, Le, D(2), Land, Sp,
            new Formula.Fraction(D(1), D(2)), Le, p, Le, D(1), Implies, Esc,
            Call("JointlyConvexOn", cone, cone,
                Seq(Lambda, Sp, x, Comma, Sp, y, Mapsto,
                    Call("tracePower", new Formula.Fraction(D(1), p),
                        Call("geometricMean", a, Call("rpow", x, p), Call("rpow", y, p))))));
    }
}
