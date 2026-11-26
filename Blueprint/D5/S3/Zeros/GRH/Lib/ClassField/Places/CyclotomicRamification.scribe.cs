using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class CyclotomicRamificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclotomic Ramification", H("Cyclotomic Ramification"),
        Blocks(
            Paragraph(Text("Cyclotomic p-power tower of Q_p is totally ramified; inertia hits each cyclotomic value.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/CyclotomicRamification.exists_inertia_cyclotomicGp_eq"),
                H("exists_inertia_cyclotomicGp_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Every natural number a prime to p is the value of the cyclotomic character at some element of the inertia group of G_p; that is, ℚ_p(μ_{p^∞}) is totally ramified.")))))));
}
