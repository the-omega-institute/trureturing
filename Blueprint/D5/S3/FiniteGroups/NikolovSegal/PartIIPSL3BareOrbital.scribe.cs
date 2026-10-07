using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL3BareOrbitalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSL3 BareOrbital.",
        H("Actual PSL3 BareOrbital"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3bareorbital-actual-bare-psl3-orbital-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3BareOrbital.actual_bare_PSL3_orbital_product"),
                H("actual bare PSL3 orbital product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q>0, M>q(4q+1), and finite field size greater than 4(4q+1)^q, arbitrary bare PSL3 automorphisms in three M-blocks and positive divisors e of q admit one actual projective correction tuple before every actual projective U3 target. Actual corrected factor tuples give the ordered three-block q/e-powered PRODUCT, using the derived U action model and proved power preservation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3bareorbital-actual-bare-psl3-ordered-orbital-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3BareOrbital.actual_bare_PSL3_ordered_orbital_product"),
                H("actual bare PSL3 ordered orbital product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same scalar bounds and divisor hypotheses, arbitrary bare PSL3 automorphisms indexed by Fin(3M) admit one projective correction tuple before all actual projective U3 targets. The genuine factor tuple produces the increasing-index ordered q/e-powered PRODUCT; the exact three-block order is retained."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.")))));
}
