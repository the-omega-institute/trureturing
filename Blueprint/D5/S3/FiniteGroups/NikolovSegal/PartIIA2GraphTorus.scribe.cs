using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2GraphTorusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2GraphTorus.",
        H("Part II A2GraphTorus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-tau-coe"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_coe"),
                H("tau coe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual graph automorphism sends g to its inverse transpose with both matrix indices reversed by Fin.revPerm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-tau-involutive"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_involutive"),
                H("tau involutive"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying the inverse-transpose and reversed-index graph automorphism twice returns the original determinant-one matrix, over every field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-tau-sq"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_sq"),
                H("tau sq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual graph automorphism tau has square equal to the identity automorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-tau-t01"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T01"),
                H("tau T01"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The graph automorphism sends the actual (0,1) transvection with parameter t to the (1,2) transvection with parameter -t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-tau-t12"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T12"),
                H("tau T12"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The graph automorphism sends the actual (1,2) transvection with parameter t to the (0,1) transvection with parameter -t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-tau-t02"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T02"),
                H("tau T02"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The graph automorphism sends the central (0,2) transvection with parameter t to the same root with parameter -t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-h-coe"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_coe"),
                H("H coe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero lambda, the determinant-one torus element H is the actual diagonal matrix with entries lambda^2, lambda inverse, lambda inverse."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-h-det"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_det"),
                H("H det"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero lambda, the diagonal matrix with entries lambda^2, lambda inverse, lambda inverse has determinant one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-h-inv-coe"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_inv_coe"),
                H("H inv coe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse of H(lambda) has diagonal entries (lambda inverse)^2, lambda, lambda."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-h-conj-t01"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T01"),
                H("H conj T01"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation by H(lambda), for nonzero lambda, multiplies the actual (0,1) root parameter by lambda^3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-h-conj-t12"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T12"),
                H("H conj T12"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation by H(lambda), for nonzero lambda, fixes every actual (1,2) transvection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-h-conj-t02"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T02"),
                H("H conj T02"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation by H(lambda), for nonzero lambda, multiplies the central (0,2) root parameter by lambda^3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-isolating-graph-square"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.isolating_graph_square"),
                H("isolating graph square"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose a genuine automorphism exchanges the two simple roots with parameters chi0*phi(t) and chi1*phi(t). For nonzero lambda, the square of conj(H(lambda))*beta acts on the first simple root by lambda^3*chi1*phi(chi0)*phi^2(t). The same field automorphism and both signed root transports are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2graphtorus-isolating-tau-square-t01"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.isolating_tau_square_T01"),
                H("isolating tau square T01"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual graph automorphism tau and nonzero lambda, the square of conj(H(lambda))*tau sends the first simple-root parameter t to lambda^3*t."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
