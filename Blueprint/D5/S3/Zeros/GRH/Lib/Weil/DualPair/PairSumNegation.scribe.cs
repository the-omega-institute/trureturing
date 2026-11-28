using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class PairSumNegationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair Sum Negation", H("Pair Sum Negation"),
        Blocks(
            Paragraph(Text("Finite-place action of a dual pair on data; explicit scalars at split places. Theta functional is canonical, transported by isometries, multiplicative on orthogonal sums. Theta kernels under orthogonal sums (seesaw factorisation) and negation of the form.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairSumNegation.pairWeil_boxProd_target"),
                H("pairWeil_boxProd_target"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If g is block diagonal with blocks g₁, g₂ along the splitting e of coordinates, then on Hom(T,V), ω_{a,bb'}(h,g)(f ⊠ f') = ω_{a,b}(h,g₁)f ⊠ ω_{a,b'}(h,g₂)f' for data f, f' on Hom(T,V₁), Hom(T,V₂).")))))));
}
