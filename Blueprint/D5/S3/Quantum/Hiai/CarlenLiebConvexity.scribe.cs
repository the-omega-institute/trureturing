using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class CarlenLiebConvexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Carlen-Lieb fixed-congruence trace convexity by explicit optimizer interpolation.",
        H("CarlenLiebConvexity"), Blocks(
            Describe.Lean(DescribeId.Create("fixed-congruence-trace-convexity"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/CarlenLiebConvexity.fixed_congruence_trace_convex"),
                H("Full fixed-congruence convexity supplier"), StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/carlenlieb2008minkowski")),
                Blocks(Paragraph(Text("For 1 <= a <= 2 and every fixed invertible complex "
                    + "square Z, X maps to Re Tr((Z* X to exponent a Z) to exponent "
                    + "1/a) is convex on the positive definite cone. X and Z need "
                    + "not commute, Z need not be selfadjoint, and every finite "
                    + "dimension including the empty one is covered. All powers "
                    + "use spectral continuous functional calculus.")),
                    Paragraph(Text("For each endpoint X choose the attained Young "
                    + "optimizer W=(Z* X to exponent a Z) to exponent 1/a. Invertibility "
                    + "of Z ensures this congruence and W are positive definite. "
                    + "Their affine mixture remains positive definite. Bound the "
                    + "target at the mixture by the reverse Young objective there, "
                    + "then apply joint trace perspective convexity and the affine "
                    + "trace penalty. Endpoint equality gives the weighted endpoint "
                    + "values; cancellation of a > 0 finishes convexity. No "
                    + "convexity supplier is assumed as a theorem hypothesis.")),
                    Paragraph(Text("The trace perspective consumes the new generic "
                    + "C-star power-convexity proof, its all-Hilbert CondIciAll, the "
                    + "public Jensen perspective and the existing phiK bridge. "
                    + "The Young bound and minimum consume general Schatten Holder "
                    + "at positive exponents, including those below one. Only "
                    + "helpers on these real proof paths are retained.")),
                    Paragraph(Text("This is classical Carlen-Lieb Theorem 1.1 at q=1, "
                    + "not an original mathematical inequality. For Hiai take a=2p; "
                    + "the entire required 1/2 <= p < 1 range lies in this supplier's "
                    + "interval. The other curvature supplier, inverse geometric-mean "
                    + "identification, full parameter assembly and source support "
                    + "constraint at the semidefinite boundary remain required. "
                    + "Original problem count is unchanged. Native four-slot audit "
                    + "remains unfinished under #5214: no faithful enrolled template "
                    + "supplies the complete universe-polymorphic matrix telescope "
                    + "with original source reconstruction and variation/sensitivity "
                    + "evidence. No declared_validated status is claimed."))), DescribeRole.Theorem))));
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
        var d = F.Id("d"); var a = F.Id("a"); var z = F.Id("Z"); var x = F.Id("X");
        var matrix = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        var reciprocal = new Formula.Fraction(D(1), a);
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Sp,
            d, Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            a, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp, z, Colon, Sp, matrix, Comma, Esc,
            D(1), Le, Sp, a, Le, Sp, D(2), Land, Sp, Call("IsUnit", z), Implies, Esc,
            Call("ConvexOn", Seq(Mathbb, Grp(F.Id("R"))), Call("PosDefCone", matrix),
                Seq(Lambda, Sp, x, Mapsto, Call("tracePower", reciprocal,
                    Seq(Call("adjoint", z), Call("rpow", x, a), z)))));
    }
}
