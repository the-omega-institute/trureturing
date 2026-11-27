using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class UpsilonValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Upsilon Values", H("Upsilon Values"),
        Blocks(
            Paragraph(Text("Splitting character and Weil data: imaginary element, self-dual idele, inert sign. Local values of Hecke characters, evaluation of splitting character; ideals principal in integral adeles.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/UpsilonValues.exists_reduction_and_idele_generator"),
                H("exists_reduction_and_idele_generator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a nonzero ideal I of O_E, reduction mod I extends to ρ: Ô → O_E/I with kernel IÔ = tÔ, for an integral finite idele t that is 1 off I and has order ord_w(I) at w; moreover Iy ⊂ Ô iff ty ∈ Ô.")))))));
}
