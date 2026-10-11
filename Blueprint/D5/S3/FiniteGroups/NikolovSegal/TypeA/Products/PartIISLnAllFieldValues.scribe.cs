using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISLnAllFieldValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn All Field Values.",
        H("Type-A SLn All Field Values"),
        Blocks(
            Paragraph(Text("For every finite field with |F|<=K, the characteristic-two and size-greater-than-two whole-group classifications feed the original finite-outer value construction. The q/e powers and correction-before-all-witnesses order remain exact; the explicit class width is consumed in the subsequent small-field product.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnallfieldvalues-actual-bare-sln-all-field-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnAllFieldValues.actual_bare_SLn_all_field_values"),
                H("actual bare SLn all field values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite-outer consumer for arbitrary bare SLn actions in the stated field/rank branch, with no normal-form/fixed-root premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnallfieldvalues-actual-bare-psln-all-field-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnAllFieldValues.actual_bare_PSLn_all_field_values"),
                H("actual bare PSLn all field values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intrinsic PSLn counterpart: the finite outer image is constructed; the bare automorphisms and their inner corrections are never lifted."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
