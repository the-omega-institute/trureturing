using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL3ModelCorrectionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSL3 ModelCorrections.",
        H("Actual PSL3 ModelCorrections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3modelcorrections-actual-normalizing-a2-model-orbital-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3ModelCorrections.actual_normalizing_A2_model_orbital_product"),
                H("actual normalizing A2 model orbital product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q>0, M>q(4q+1), and finite field size greater than 4(4q+1)^q, arbitrary genuine diagonal/field/graph tuples and positive divisor tuple e admit one actual SL3 correction tuple. Each corrected automorphism preserves actual U3, and every actual U3 target is an ordered product of the original q/e-powered corrected values. The correction is chosen before all targets; the preservation condition is proved and supports projective power transport."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.")))));
}
