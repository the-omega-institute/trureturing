using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Unitriangular Reconstruction.",
        H("Type-A Unitriangular Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularreconstruction-actual-proper-commutator-layer-reconstruction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularReconstruction.actual_proper_commutator_layer_reconstruction"),
                H("actual proper commutator layer reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full actual unitriangular reconstruction from printed PartII equation(13). For every fixed proper g, its single commutator-value map from the kth layer covers the ENTIRE (k+1)st layer, for arbitrary rank and every field. The finite induction solves all remaining higher coordinates, retaining the noncommutative conjugation terms rather than commuting them away. This is the proper-matrix kernel; Lemma9.1 and semilinear powered assembly remain required for the uniform Proposition6.5 supplier."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
