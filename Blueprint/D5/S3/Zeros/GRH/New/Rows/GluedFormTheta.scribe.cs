using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class GluedFormThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Glued Form Theta", H("Glued Form Theta"),
        Blocks(
            Paragraph(Text("Some jet with indicator datum is no more divisible than predicted, at every prime. Glued lattices at the level primes and the product forms from which the comparison forms are built. Theta descent of the comparison forms is an average of products of two kernels.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/GluedFormTheta.theta_stdClassSum_productForm"),
                H("theta_stdClassSum_productForm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If DividedSplitting.IsGlued s L and bb′ = O.b, the theta lift at g of ∑_h DividedSplitting.productForm(h, h′)(conj(c·y(h)), η), class sum at level rowFixingLevel, is conj(β_L c)·∑_Y conj(cosetKernelSum(y)·θ^{W,V°}[1_{inc z}, η̄](·, h′)) at gỸ, over Y ∈ GL_r(O/M²), Y ≡ 1 mod M, Ỹ lifts.")))))));
}
