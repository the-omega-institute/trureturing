using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class MatrixTracePerspectiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint trace perspective convexity for noncommuting finite matrices.",
        H("MatrixTracePerspective"), Blocks(
            Describe.Lean(DescribeId.Create("matrix-trace-perspective"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/MatrixTracePerspective.trace_perspective_jointly_convex"),
                H("Matrix trace perspective with both adjoints"), StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(Paragraph(Text("For every finite complex square dimension, "
                    + "1 <= a <= 2 and arbitrary complex Z, Re Tr(Z* X to exponent a "
                    + "Z W to exponent 1-a) is jointly convex on positive definite "
                    + "X and W. Z need not be selfadjoint or invertible. Empty "
                    + "dimension is split before the Hilbert Nontrivial instances.")),
                    Paragraph(Text("The star algebra equivalence Matrix.toEuclideanCLM "
                    + "transports positivity, CFC spectral powers, products, both "
                    + "adjoints, trace and affine mixtures. Apply the consumed trace "
                    + "perspective theorem with K=star Z, then cyclically move the "
                    + "adjoint in the trace. The proof reuses the original phiK "
                    + "spectral bridge and does not change its multiplication order.")),
                    Paragraph(Text("This is a consumed interface for the Carlen-Lieb "
                    + "convexity proof, not new mathematics independent of that proof. "
                    + "Native audit exception #5214 applies to the missing lawful "
                    + "matrix-telescope template, full source reconstruction and "
                    + "variation/sensitivity evidence; no declared_validated status "
                    + "is claimed. Classical source attribution is Apache-2.0."))), DescribeRole.Theorem))));
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
    private static Formula Endpoint()
    {
        var d = F.Id("d"); var a = F.Id("a"); var z = F.Id("Z");
        var x = F.Id("X"); var w = F.Id("W");
        var matrix = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Sp,
            d, Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            a, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp, z, Colon, Sp, matrix, Comma, Esc,
            D(1), Le, Sp, a, Le, Sp, D(2), Implies, Esc,
            Call("JointlyConvexOn", Call("PosDefCone", matrix), Call("PosDefCone", matrix),
                Seq(Lambda, Sp, x, Comma, Sp, w, Mapsto,
                    Call("ReTr", Seq(Call("adjoint", z), Call("rpow", x, a), z,
                        Call("rpow", w, Seq(D(1), Minus, a)))))));
    }
}
