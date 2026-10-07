using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47TypeIIDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cycle boundaries and genuine commutator values.",
        H("Cycle boundaries and genuine commutator values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typeii-cycle-value-with-witness-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeII.cycle_value_with_witness_iff"),
                H("cycle value with witness iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary group and a periodic permutation cycle, prescribing the base scalar u characterizes the genuine commutator values by the ordered cycle boundary. No inverse relation between different component automorphisms is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typeii-corrected-value-tuple-with-parameters-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeII.corrected_value_tuple_with_parameters_iff"),
                H("corrected value tuple with parameters iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite coordinate type and the actual coordinate law, the q-powered inner corrections and prescribed base scalars satisfy the cycle boundaries exactly when there is a genuine corrected factor tuple."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
