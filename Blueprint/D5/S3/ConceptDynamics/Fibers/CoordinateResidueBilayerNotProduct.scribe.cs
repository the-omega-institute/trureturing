using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class CoordinateResidueBilayerNotProductDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Fibers/CoordinateResidueBilayerNotProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-point bilayer decomposes into dependent coordinate fibers but not into a "
            + "uniform product; uniform fiber equivalences suffice for a product decomposition.",
        H("Coordinate Residue Bilayer Is Not a Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinate-residue-bilayer-not-product"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "coordinate_residue_bilayer_not_product"),
                H("Unequal coordinate residues obstruct a uniform product"),
                StatementSource.FromAuthor(BilayerObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The false coordinate carries one residual point, while the true "
                            + "coordinate carries two. Their dependent sum therefore has three "
                            + "points, and reading the coordinate gives its canonical dependent-"
                            + "fiber decomposition.")),
                    Paragraph(Text(
                        "A hypothetical product with the two-point Boolean coordinate would "
                            + "have twice as many points as its residue type. Finiteness of that "
                            + "residue follows from the hypothetical equivalence, so its product "
                            + "cannot have the bilayer's odd cardinality of three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-decomposition-of-uniform-residues"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "product_decomposition_of_uniform_residues"),
                H("Uniform residues yield a product decomposition"),
                StatementSource.FromAuthor(UniformResiduesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose every fiber of a readout is equipped with an equivalence to "
                            + "one fixed residue type. These equivalences assemble the dependent "
                            + "sum of the fibers into the ordinary product of the coordinate and "
                            + "residue types.")),
                    Paragraph(Text(
                        "Composing this assembly with the canonical dependent-fiber "
                            + "decomposition recovers the source as that product. The condition "
                            + "needs no finiteness assumption and isolates a sufficient uniformity "
                            + "condition absent from the bilayer counterexample."))),
                DescribeRole.Lemma))));

    private static Formula BilayerObstructionFormula()
    {
        Formula bilayer = F.Id("BilayerObject");
        Formula coordinateType = F.Id("Bool");
        Formula coordinate = F.Id("b");
        Formula concept = F.Id("bilayerConcept");
        Formula residueType = F.Id("R");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula fiber = Call("ConceptFiber", concept, coordinate);
        Formula dependentFibers = Seq(
            Sum, Sp, Underscore, Grp(coordinate, Colon, Sp, coordinateType), Sp, fiber);
        Formula dependentDecomposition = Call(
            "Nonempty", Seq(bilayer, Sp, Equiv, Sp, dependentFibers));
        Formula productDecomposition = Call(
            "Nonempty",
            Seq(bilayer, Sp, Equiv, Sp, coordinateType, Sp, Times, Sp, residueType));

        return Disp(Seq(
            dependentDecomposition, Sp, Land, Sp,
            Forall, Sp, residueType, Colon, Sp, type, Comma, Sp,
            Neg, Sp, productDecomposition, Dot));
    }

    private static Formula UniformResiduesFormula()
    {
        Formula source = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula residueType = F.Id("R");
        Formula readout = F.Id("q");
        Formula coordinate = F.Id("b");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula uniformity = Seq(
            Forall, Sp, coordinate, Colon, Sp, coordinateType, Comma, Sp,
            Call("ConceptFiber", readout, coordinate), Sp, Equiv, Sp, residueType);
        Formula productDecomposition = Call(
            "Nonempty",
            Seq(source, Sp, Equiv, Sp, coordinateType, Sp, Times, Sp, residueType));

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coordinateType, Comma, Sp,
            residueType, Colon, Sp, type, Comma, Sp,
            readout, Colon, Sp, source, Sp, To, Sp, coordinateType, Comma, Sp,
            Grp(uniformity), Sp, Rightarrow, Sp, productDecomposition, Dot));
    }
}
