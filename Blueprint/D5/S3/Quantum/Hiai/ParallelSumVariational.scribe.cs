using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class ParallelSumVariationalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The matrix parallel sum as an attained quadratic split minimum.",
        H("ParallelSumVariational"), Blocks(
            Describe.Lean(DescribeId.Create("parallel-sum-minimum"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/ParallelSumVariational.parallel_sum_minimum"),
                H("A common split domain in Loewner order"), StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let P and Q be positive definite complex square matrices, "
                    + "H = (P inverse + Q inverse) inverse, and K any complex square matrix. "
                    + "For every split U + V = K, the energy U* P U + V* Q V dominates K* H K "
                    + "in the actual Loewner order. The split U = P inverse H K and "
                    + "V = Q inverse H K attains equality.")),
                    Paragraph(Text("Subtracting the minimum energy gives the sum of the two "
                    + "positive quadratic energies of U minus its optimizer and V minus its "
                    + "optimizer. The two cross terms cancel because the split shares the "
                    + "same K. No commutation, selfadjointness or invertibility is required "
                    + "of K, U or V.")),
                    Paragraph(Text("This is the matrix minimum needed by the real variational "
                    + "candidate route to the Hiai outer-power concavity supplier. Setting "
                    + "P to t inverse times B to exponent p and Q to A to exponent p gives "
                    + "the weighted inverse sum. The next obligations are the weighted trace "
                    + "minimum, its joint concavity using the existing Lieb theorem, the "
                    + "geometric-mean integral, and the trace Legendre maximum. This theorem "
                    + "does not assert those analytic steps or resolve Hiai Problem 5.18."))),
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

    private static Formula Energy(Formula p, Formula q, Formula u, Formula v) =>
        Seq(Call("adjoint", u), p, u, Plus, Call("adjoint", v), q, v);

    private static Formula Endpoint()
    {
        var d = F.Id("d"); var p = F.Id("P"); var q = F.Id("Q"); var k = F.Id("K");
        var z = F.Id("Z"); var w = F.Id("W");
        var u = Call("fst", z); var v = Call("snd", z);
        var a = Call("fst", w); var b = Call("snd", w);
        var h = Call("parallelSum", p, q);
        var matrix = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        var minimum = Seq(Call("adjoint", k), h, k);
        return Seq(Forall, Sp, F.Id("w"), Colon, Sp, Call("Level"), Comma, Esc,
            d, Colon, Sp, Call("Type", F.Id("w")), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            p, Comma, Sp, q, Comma, Sp, k, Colon, Sp, matrix, Comma, Esc,
            Call("PosDef", p), Land, Call("PosDef", q), Implies, Esc,
            Exists, Sp, z, Colon, Sp, Call("Prod", matrix, matrix), Comma, Esc,
            u, Eq, Seq(Call("inverse", p), h, k), Land,
            v, Eq, Seq(Call("inverse", q), h, k), Land,
            u, Plus, v, Eq, k, Land, Energy(p, q, u, v), Eq, minimum, Land,
            Open, Forall, Sp, w, Colon, Sp, Call("Prod", matrix, matrix), Comma, Esc,
            a, Plus, b, Eq, k, Implies, minimum, Le, Energy(p, q, a, b), Close);
    }
}
