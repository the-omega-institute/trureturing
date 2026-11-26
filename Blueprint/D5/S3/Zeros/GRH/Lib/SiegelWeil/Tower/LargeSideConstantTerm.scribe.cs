using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.Tower;

internal sealed class LargeSideConstantTermDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Large Side Constant Term", H("Large Side Constant Term"),
        Blocks(
            Paragraph(Text("Constant term of lifted character equals smaller lift times explicit Hecke L-value factor.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/LargeSideConstantTerm.exists_constant_term_thetaLarge"),
                H("exists_constant_term_thetaLarge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Removing a plane, large side: for standard data, the constant term along A of the theta integral for (W′, V′) is γ times that for (W, V) with a cone integral as real datum, where |γ|²Π(e) = CΠ(e+1), e = rk V − rk W/2, C free of 𝔠.")))))));
}
