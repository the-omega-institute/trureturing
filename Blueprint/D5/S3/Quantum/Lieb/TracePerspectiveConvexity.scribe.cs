using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class TracePerspectiveConvexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ando trace perspective convexity from the actual uniform Jensen input.",
        H("TracePerspectiveConvexity"), Blocks(
            Describe.Lean(DescribeId.Create("trace-perspective-convexity"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/TracePerspectiveConvexity.trace_perspective_jointly_convex"),
                H("Joint trace perspective convexity"), StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(Paragraph(Text("For 1 <= a <= 2 and arbitrary bounded K on any "
                    + "complete nontrivial finite dimensional complex Hilbert space, "
                    + "Re Tr(A to exponent a K* B to exponent 1-a K) is jointly "
                    + "convex for positive definite A and B. K need not be invertible "
                    + "or selfadjoint. This consumed supplier transports to square "
                    + "matrices and feeds explicit Carlen-Lieb optimizer interpolation.")),
                    Paragraph(Text("Apply the public generalized perspective theorem "
                    + "to the actual all-Hilbert CondIciAll for x to exponent a and "
                    + "the affine second function x to exponent one. Transfer affine "
                    + "mixtures through the Hilbert-Schmidt left and right multipliers, "
                    + "then apply the positive quadratic functional phiK. The existing "
                    + "public phiK_operatorPowerMean_eq_liebTraceMap supports unrestricted "
                    + "real exponents and supplies the exact trace identity. No joint "
                    + "eigenbasis proof or private CondV core is reproved.")),
                    Paragraph(Text("Right multiplication is an antihomomorphism and its "
                    + "star algebra homomorphism has opposite domain. The second "
                    + "perspective input remains the base. For a quadratic vector Z "
                    + "the trace transport uses K=star Z. Physlib source reuse is "
                    + "Apache-2.0 and the mathematics is classical. Native audit "
                    + "remains unfinished under #5214: the full dependent Hilbert "
                    + "telescope lacks a supplied lawful template with rigid universe "
                    + "reconstruction and variation/sensitivity evidence. No "
                    + "declared_validated status or full Hiai resolution is claimed."))),
                DescribeRole.Theorem))));
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
        var h = F.Id("H"); var a = F.Id("a"); var k = F.Id("K");
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Sp,
            h, Colon, Sp, Call("Type", F.Id("u")), Comma, Esc,
            OpenBracket, Call("NormedAddCommGroup", h), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", Seq(Mathbb, Grp(F.Id("C"))), h), CloseBracket,
            Comma, Sp, OpenBracket, Call("CompleteSpace", h), CloseBracket, Comma, Esc,
            OpenBracket, Call("FiniteDimensional", Seq(Mathbb, Grp(F.Id("C"))), h), CloseBracket,
            Comma, Sp, OpenBracket, Call("Nontrivial", h), CloseBracket, Comma, Esc,
            a, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp,
            k, Colon, Sp, Call("L", h), Comma, Esc, D(1), Le, Sp, a, Le, Sp, D(2), Implies, Esc,
            Call("JointlyConvexOn", Call("pdSet", h), Call("pdSet", h), Call("liebTraceMap", a, k)));
    }
}
