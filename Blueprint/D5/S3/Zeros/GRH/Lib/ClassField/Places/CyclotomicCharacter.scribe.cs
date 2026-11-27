using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class CyclotomicCharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclotomic Character", H("Cyclotomic Character"),
        Blocks(
            Paragraph(Text("Basic properties of decomposition groups, inertia groups and Frobenius elements. Cyclotomic characters: values on Frobenius and inertia; continuity, surjectivity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/CyclotomicCharacter.map_cycChar_smul"),
                H("map_cycChar_smul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Ω be algebraically closed of characteristic 0, A a ℤ_l-module and f : A → B additive with image killed by l^r. Then f(χ_l(σ)x) = χ_{l^r}(σ)·f(x), with χ_l the l-adic and χ_{l^r} the mod l^r cyclotomic character.")))))));
}
