using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PauliFixedProductFamilyDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(Comma, args), Close);
    private static Formula Join(Formula separator, Formula[] items) =>
        items.Length == 0 ? Seq() : Seq(items.SelectMany((x, i) =>
            i == 0 ? new[] { x } : new[] { separator, x }).ToArray());
    private static Formula V(string name) => F.Id(name);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed positive tensor product carries a real Pauli perturbation with a complete unaveraged residual.",
        H("Fixed spin products and the full Pauli residual"),
        Blocks(
            Paragraph(Text("The local space is real Euclidean four-space, ordered as scalar, x, y, z. "
                + "Its spin multiplication sends (a,v),(b,w) to (ab+v dot w, aw+bv). "
                + "The fixed cross channel sends them to (0,v cross w). "
                + "The local action at real parameter t replaces the first cross label v by v+taz. "
                + "The local and joint inner products and both multiplications are independent of t.")),
            Paragraph(Text("The joint carrier is the real Hilbert tensor product of the two local spaces. "
                + "Its multiplication is spin tensor spin minus cross tensor cross; the cross channels in this product are fixed. "
                + "The joint action on a simple label is D tensor left multiplication plus left multiplication tensor D. "
                + "Bilinear maps and the tensor universal property extend these formulas to every joint input. "
                + "The residual is Gamma applied to the product, minus the two product terms obtained by applying Gamma to one input.")),
            Describe.Lean(DescribeId.Create("complete-ordered-residual"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PauliFixedProductFamily.full_report"),
                H("Every ordered report label and every output coordinate"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, V("t"), Sp, InMacro, Sp,
                    Mathbb, Grp(V("R")), Comma, Sp,
                    Call("reportSquared", V("t")), Sp, Eq, Sp, D(2,8,8), Sp,
                    V("t"), Caret, Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The report sums squared norms over all three copies of the complete sixteen-element product basis. "
                        + "There is no average over the 4096 ordered triples, and each output norm already sums every output coordinate. "
                        + "Six first-input blocks contribute forty-eight times t squared each; all ten remaining blocks vanish. "
                        + "The block values are evaluated from the actual bilinear product and actual joint action.")),
                    Paragraph(Text("This is a finite dimensional algebraic realization. It supplies neither an experimental acquisition procedure "
                        + "nor a general stability theorem for arbitrary joint products, and it implies no physical reconstruction at positive residual."))),
                DescribeRole.Theorem))));
}
