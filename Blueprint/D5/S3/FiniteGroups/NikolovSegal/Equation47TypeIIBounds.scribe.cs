using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47TypeIIBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cycle and movement counts.",
        H("Actual cycle and movement counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typeiibounds-actual-cycle-count-bound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIBounds.actual_cycle_count_bound"),
                H("actual cycle count bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a permutation of a finite type, twice the number of genuine cycles is at most the number of points plus the number of fixed points."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typeiibounds-typeii-cycle-budget"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIBounds.typeII_cycle_budget"),
                H("typeII cycle budget"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least two, movement at least (4+2D)n gives the cycle inequality needed for type-II reconstruction."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
