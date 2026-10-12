using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class HolderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Product Schatten Holder inequality for arbitrary square complex matrices.",
        H("Holder"), Blocks(
            Describe.Lean(DescribeId.Create("product-holder"),
                DeclarationHandle.Create("D5/S3/Quantum/Schatten/Holder.schattenNorm_mul_le"),
                H("Every positive exponent"), StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/meiburg2026schatten")),
                Blocks(Paragraph(Text("For r, p, q positive with 1/r = 1/p + 1/q, "
                    + "the Schatten r norm of AB is at most the product of the Schatten p "
                    + "norm of A and the Schatten q norm of B. The index type is arbitrary "
                    + "finite and decidable; the empty case is included. No Hermitian, "
                    + "positivity, invertibility or commutation assumption is imposed on A or B.")),
                    Paragraph(Text("The norm is the real trace of the spectral power p/2 "
                    + "of the Gram matrix A* A, raised to 1/p. The proof bounds singular-value "
                    + "power sums through Horn log-majorization and finite scalar Holder. "
                    + "All real spectral powers are the finite matrix functional calculus.")),
                    Paragraph(Text("This is attributed reuse of Alex Meiburg's Apache-2.0 "
                    + "Physlib proof at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142. "
                    + "It supplies the arbitrary-product inequality needed for the inverse-mean "
                    + "trace variational formula; it alone asserts no Hiai joint convexity."))),
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
        var d = F.Id("d"); var a = F.Id("A"); var b = F.Id("B");
        var r = F.Id("r"); var p = F.Id("p"); var q = F.Id("q");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Esc,
            d, Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            a, Comma, Sp, b, Colon, Sp, Call("Matrix", d, d, complex), Comma, Esc,
            r, Comma, Sp, p, Comma, Sp, q, Colon, Sp, real, Comma, Esc,
            D(0), Lt, r, Land, D(0), Lt, p, Land, D(0), Lt, q, Land,
            Seq(Frac, Grp(D(1)), Grp(r)), Eq, Seq(Frac, Grp(D(1)), Grp(p)), Plus, Seq(Frac, Grp(D(1)), Grp(q)),
            Implies, Esc, Call("schattenNorm", Seq(a, b), r), Le,
            Call("schattenNorm", a, p), Times, Call("schattenNorm", b, q));
    }
}
