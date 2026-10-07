using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47ValueNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalization by actual cycle-base values.",
        H("Normalization by actual cycle-base values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47valuenormalization-normalizedvalues-cycle-constraints"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47ValueNormalization.normalizedValues_cycle_constraints"),
                H("normalizedValues cycle constraints"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized values satisfy each genuine cycle boundary with its prescribed base scalar."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47valuenormalization-normalized-system-iff-actual"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47ValueNormalization.normalized_system_iff_actual"),
                H("normalized system iff actual"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Solving every normalized vertex word is equivalent to solving the ordered product of genuine commutator values, with the same independently prescribed cycle-base scalars."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
