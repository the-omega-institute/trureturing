using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47TypeIIFibresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Genuine corrected factor-tuple fibre lower bounds.",
        H("Genuine corrected factor-tuple fibre lower bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typeiifibres-actual-connected-fixed-cycle-fibre-bound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIFibres.actual_connected_fixed_cycle_fibre_bound"),
                H("actual connected fixed cycle fibre bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite S and I, n at least two, a connected q-powered graph and the genuine cycle inequality sum(cycles)+2n+2D at most mn, fix arbitrary y and all actual cycle-base scalars. Under the twisted PRODUCT input, the fibre of genuine corrected factor tuples has cardinality at least |S| raised to (mn minus sum(cycles) minus (n minus one) minus 2D). Restriction reads actual corrected commutator values at unused nonbase coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typeiifibres-actual-connected-typeii-fibre-bound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIFibres.actual_connected_typeII_fibre_bound"),
                H("actual connected typeII fibre bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cycle-base parameters are uniquely determined by each genuine tuple. Summing their disjoint fibres gives at least |S| raised to (mn minus (n minus one plus 2D)) corrected tuples for every target, with the same arbitrary fixed y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typeiifibres-actual-connected-proposition9-1-count"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIFibres.actual_connected_proposition9_1_count"),
                H("actual connected proposition9 1 count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive D under the same genuine cycle inequality and twisted PRODUCT premise, |S| raised to mn is at most the corrected fibre cardinality times |S| raised to 4Dn. This is the centreless connected count, not a quasisimple central-cover theorem."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
