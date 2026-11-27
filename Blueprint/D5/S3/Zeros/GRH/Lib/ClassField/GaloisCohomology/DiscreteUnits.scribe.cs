using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology;

internal sealed class DiscreteUnitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discrete Units", H("Discrete Units"),
        Blocks(
            Paragraph(Text("Module over Z/l^r with small l-torsion admits primitive relation with prescribed zeros. Discrete modules with continuous action, restriction, exact sequences, functions on finite sets. Counting in exact sequences; left exactness of continuous 1-cocycles. Trivialised cocycles: extension from orbit representatives, corestriction, submultiplicative count in exact sequences. Additive notation for the multiplicative group of the algebraic closure.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/DiscreteUnits.card_le_of_isShortExact"),
                H("card_le_of_isShortExact"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For 0 → A → B → C → 0 exact: if the trivialised cocycles DiscreteModule.trivialisedCocycles of A and C are finite in number, at most (#A)^k and (#C)^k, likewise for B; equality for B forces surjectivity onto those of C and equality for A.")))))));
}
