using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Columns;

internal sealed class TwistedHeckeTypeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twisted Hecke Type", H("Twisted Hecke Type"),
        Blocks(
            Paragraph(Text("Valuation at N of character factors and of data given modulo N. Chain with denominators N equals scalar times chain mod N after Gauss-sum operator. Valuation of the restricted chain at the level prime N on a submodule. Scaled Hecke operator on algebraic forms has elementary divisors of small mean exponent.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Columns/TwistedHeckeType.hasType_markOperator"),
                H("hasType_markOperator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let l lie in a marked set Λ, T be twisting data on the tops inducing l or l̄, and HeckeSizes hold. Then Y = Data.IsMarked.markOperator keeps the integral columns 𝒜, and [𝒜 : Y𝒜 + p^s𝒜] ∣ p^c, c ≤ (z + xs + y)·dim.")))))));
}
