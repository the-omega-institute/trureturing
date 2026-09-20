using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class PrimeCyclotomicTraceImageDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real prime-cyclotomic trace Gram template has an exact integral-image "
            + "criterion and a unique, explicitly reconstructed integer preimage.",
        H("Integral Image of the Prime-Cyclotomic Trace Template"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-cyclotomic-trace-gram-action"),
                DeclarationHandle.Create(Prefix + "traceGram"),
                H("Actual integer matrix action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n>=0 write an integer vector as (x0,x), with x indexed by Fin n, "
                        + "and put m=2*n+3. The zeroth output is (n+1)*x0-sum(x); "
                        + "the ith output is m*x(i)-x0-2*sum(x). At a prime m this is "
                        + "the trace Gram matrix of the real m-cyclotomic field. "
                        + "CTG.3 also identifies it with the complete nontrivial p-power "
                        + "tower when m=p^k, including composite m. The definition "
                        + "makes no primality assumption and includes n=0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-cyclotomic-trace-reconstruction"),
                DeclarationHandle.Create(Prefix + "reconstruct"),
                H("Integer-division reconstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For y=(y0,y), set z(i)=(y(i)-2*y0)/(2*n+3), using integer division. "
                        + "The reconstructed zeroth coordinate is y0+sum(z), and the "
                        + "ith coordinate is y0+sum(z)+z(i). This is a specified integer "
                        + "vector for every y. The theorem gives exactly the domain on "
                        + "which it is a correct preimage."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-cyclotomic-trace-integral-image"),
                DeclarationHandle.Create(Prefix + "integral_image"),
                H("Exact image and unique constructive inverse"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n and every y in Z x (Fin n -> Z), all "
                            + "differences y(i)-2*y0 are divisible by 2*n+3 exactly when "
                            + "the displayed reconstruction maps to y and every integer "
                            + "preimage equals that reconstruction. Neither an inverse "
                            + "matrix nor a determinant nor a trace-dual basis is supplied "
                            + "as a theorem hypothesis.")),
                    Paragraph(Text(
                        "The proof derives the coordinate difference identity "
                            + "output(i)-2*output(0)=(2*n+3)*(x(i)-x0). Divisibility "
                            + "therefore determines all differences in a preimage. The "
                            + "zeroth row then determines x0; substitution proves "
                            + "existence, and cancellation by the positive integer "
                            + "2*n+3 proves uniqueness. The reverse implication reads "
                            + "the same difference identity at the reconstructed vector.")),
                    Paragraph(Text(
                        "STL.4 identifies the prime-layer coefficient lattice; CTG.3 "
                            + "uses the same template at n=(p^k-3)/2 for the full tower. "
                            + "The product-algebra trace identification and the inter-packet "
                            + "gluing are ordinary proofs in the existing WSS dossier. "
                            + "This formal arithmetic theorem does not construct a golden "
                            + "ring-class character or decide an unknown WSS prime.")),
                    Paragraph(
                        Text("Ambient Maass construction and normalization: "),
                        Ref(LibraryNoteRef.Create("D5/L/tanaka2026maass").Value),
                        Text(". CTG retains an existing character and proves the full "
                            + "tower's congruence module Z/p^k. A normalized integral "
                            + "trace combination attains depth k; no primitive vector in "
                            + "that same lattice attains k+1. These are ordinary results, "
                            + "not extra Lean conclusions or an independent WSS witness.")),
                    Paragraph(
                        Text("Frontier comparison and the holomorphic weight restriction: "),
                        Ref(LibraryNoteRef.Create(
                            "D5/L/fretwellroberts2026eisenstein").Value),
                        Text(". Its weight-at-least-three existence results are not "
                            + "used for the weight-zero family. The current formal "
                            + "statement, formula and proof source are unchanged."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, type, Comma, Sp, body);

    private static Formula ResultFormula()
    {
        var n = V("n");
        var y = V("y");
        var x = V("x");
        var indices = Call("Fin", n);
        var vector = Call("Prod", V("Int"), Call("Function", indices, V("Int")));
        var p = Call("add", Call("mul", D(2), Call("NatCastInt", n)), D(3));
        var difference = Call("sub", Call("apply", Call("snd", y), V("i")),
            Call("mul", D(2), Call("fst", y)));
        var divisibility = All("i", indices, Call("Dvd", p, difference));
        var reconstructed = Call("reconstruct", n, y);
        var correct = Call("Eq", Call("traceGram", n, reconstructed), y);
        var unique = All("x", vector,
            Call("Implies", Call("Eq", Call("traceGram", n, x), y),
                Call("Eq", x, reconstructed)));
        return Disp(All("n", V("Nat"), All("y", vector,
            Call("Iff", divisibility, Call("And", correct, unique)))));
    }
}
