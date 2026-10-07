using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47TypeIDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real scalar PRODUCT inputs and type-I representative bounds supply one correction tuple for all targets on the actual powered components.",
        H("Conditional simultaneous type-I coverage"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typei-fill-typei-root"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeI.fill_typeI_root"),
                H("fill typeI root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let sel be a subset of a nonempty consecutive interval J. Suppose every tau(j) for j in J fixes the root and the initial root arc values in J are one. Assume scalar coverage with variables supported in sel. For every root target, replace only selected arcs sourced at the root to solve that root word, preserving all other vertex words and every arc outside that support. Splitting the generator list gives a fixed prefix A and suffix B; use the scalar target A inverse times target times B inverse."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typei-actual-typei-components-reconstruction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeI.actual_typeI_components_reconstruction"),
                H("actual typeI components reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a finite coordinate type, retain the genuine coordinate law and a fixed y. Choose a reachable root map constant on powered components. At each root assume selected indices inside a nonempty consecutive interval fixed by the q-powered permutations, and scalar coverage supported in those indices for the corrected q-step component. Every tuple target then has a corrected q-powered commutator solution. Leaf elimination solves nonroots and leaves loop arcs free; finite root filling solves each component without altering the others."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typei-selected-support-scalar"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeI.selected_support_scalar"),
                H("selected support scalar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose the genuine supported construction with a fixed y realizes every scalar target at one root and is one outside its selected generator indices and the root coordinate. If the selected indices lie in an interval whose q-powered permutations fix the root, evaluate its ordered product at that root. The result is scalar corrected-component coverage with the same selected support and the same y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47typei-actual-all-typei-from-interval"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47TypeI.actual_all_typeI_from_interval"),
                H("actual all typeI from interval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let I be finite, S any group, and q, D and M positive, with M times D times (q plus D) at most m. Assume the actual k, sigma and beta coordinate law. Choose an actual representative of every connected component of qPowerGraph. Suppose good indices give q-periodic points and fewer than D indices are bad at every component representative. For every family of good M-index selections, assume the Part-II scalar PRODUCT input with the actual accumulated component automorphisms and actual minimal periods. Then PrescribedCommutatorCoverage(I to S,q,m,k) holds: one correction tuple y is chosen before every tuple target kappa, and c may depend on kappa. This is a conditional all-type-I theorem. It supplies neither uniform finite-simple scalar existence nor the bad-choice bound on genuine type-II components."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Lemma 10.3 and equations (45)-(50), printed pages 228-231. The scalar PRODUCT premise is the input of Part II, Theorem 1.2, equivalent to Part I, Theorem 1.10; Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. These are adaptations and proofs of conditional consequences of published mathematics, with no originality claim. Uniform scalar existence, genuine type-II reconstruction, mixed representative bounds, uniform width, restricted Burnside bounds and unconditional strong completeness remain unproved.")))));
}
