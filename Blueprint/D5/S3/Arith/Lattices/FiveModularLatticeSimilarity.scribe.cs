using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class FiveModularLatticeSimilarityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Lambda-squared A4 lattice is five-modular under its Hodge map.",
        H("Five-Modular Lattice Similarity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-lambda-squared-a4-lattice-is-five-modular"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/FiveModularLatticeSimilarity."
                        + "five_modular_lattice_similarity"),
                H("The Lambda-squared A4 lattice is five-modular"),
                StatementSource.FromAuthor(SimilarityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier, lattice, Gram form, dual lattice, and Hodge map are the "
                            + "canonical concrete objects from ExactDualLatticeFormula. In "
                            + "particular, the first clause reuses that family's exact equality "
                            + "between the dual and the image of the lattice under J divided by "
                            + "five.")),
                    Paragraph(Text(
                        "Injectivity makes the named Hodge map an identification with its image, "
                            + "and the quantified Gram identity says that every pairing is scaled "
                            + "by one fifth. Thus lengths are scaled by one over the square root of "
                            + "five; this is the direct formal content of the five-modular "
                            + "similarity, not merely an equality of cardinalities.")),
                    Paragraph(Text(
                        "The remaining public clauses record that the exact ambient carrier is "
                            + "six-dimensional and that the displayed integral Gram matrix has "
                            + "determinant both five cubed and five to the power six divided by "
                            + "two. Each equality is checked on the concrete imported matrix.")),
                    Paragraph(Text(
                        "Repository search found the exact dual-lattice predecessor but no frozen "
                            + "theorem containing the similarity and determinant clauses. Pinned "
                            + "Mathlib supplies general bilinear and lattice infrastructure only; "
                            + "the finite matrix identities here are verified directly."))),
                DescribeRole.Theorem))));

    private static Formula SimilarityFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula ambient = F.Id("AmbientSpace");
        Formula dual = F.Id("dualLattice");
        Formula image = F.Id("oneFifthHodgeLattice");
        Formula hodge = F.Id("oneFifthHodgeMap");
        Formula gram = F.Id("gramForm");
        Formula gramMatrix = F.Id("integralGramMatrix");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula hodgeX = Seq(hodge, Open, x, Close);
        Formula hodgeY = Seq(hodge, Open, y, Close);
        Formula scaledPairing = Seq(
            gram, Open, hodgeX, Comma, Sp, hodgeY, Close,
            Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(5)), Sp,
            gram, Open, x, Comma, Sp, y, Close);
        Formula determinant = Seq(
            Operatorname, Grp(F.Id("det")), Open, gramMatrix, Close);

        return Disp(new Formula.Aligned([
            Seq(dual, Sp, Eq, Sp, image, Sp, Land),
            Seq(Grp(), Call("Injective", hodge), Sp, Land),
            Seq(
                Grp(), Open, Forall, Sp,
                x, Comma, Sp, y, Colon, Sp, ambient, Comma, Sp,
                scaledPairing, Close, Sp, Land),
            Seq(
                Grp(), Call("finrank", real, ambient), Sp, Eq, Sp, D(6), Sp, Land),
            Seq(
                Grp(), determinant, Sp, Eq, Sp,
                Open, D(5), Colon, integer, Close, Caret, Grp(D(3)), Sp, Land),
            Seq(
                Grp(), determinant, Sp, Eq, Sp,
                Open, D(5), Colon, integer, Close, Caret,
                Grp(D(6), Slash, D(2)), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
