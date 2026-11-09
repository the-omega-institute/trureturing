using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class TraceInverseConvexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace convexity of inverse positive matrices.", H("TraceInverseConvexity"), Blocks(
            Describe.Lean(DescribeId.Create("weighted-trace-inverse-convexity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/TraceInverseConvexity.weighted_trace_inverse_convexOn"),
                H("Weighted inverse trace on the positive cone"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite complex matrix dimension and every positive semidefinite "
                    + "witness C, the real trace Re Tr(C A⁻¹) is convex in a positive-definite "
                    + "matrix A. The proof first applies Mathlib's operator convexity of "
                    + "Ring.inverse, then uses the positive-semidefinite trace product bound "
                    + "to descend the matrix order inequality to a scalar inequality. The "
                    + "unweighted inverse trace is the identity-witness specialization."))),
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

    private static Formula Statement()
    {
        var d = F.Id("d");
        var c = F.Id("C");
        var a = F.Id("A");
        var matrix = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        return Seq(Forall, Sp, d, Colon, Sp, Call("Type"), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            c, Colon, Sp, matrix, Comma, Sp, Call("PosSemidef", c), Sp, Implies, Esc,
            Call("ConvexOn", Seq(Mathbb, Grp(F.Id("R"))),
                Call("PosDefCone", matrix),
                Seq(Lambda, Sp, a, Mapsto,
                    Call("ReTr", c, Call("inverse", a)))));
    }
}
