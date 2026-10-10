using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryWholeGraphProjectiveProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The whole-SU and actual center-quotient PSU endpoints retain positive q, divisors e(j)|q, q/e(j), single N(q),C(q) before fields/ranks>=6 above the field cutoff, arbitrary genuine D/Phi/raw graph tuples and one right-inner correction before every actual target. The raw graph action on SU is identified with the supplied field involution. PSU is literally SU modulo its center; proved quotient surjectivity transports every quotient target. No arbitrary bare automorphism lifting or classification premise is introduced.",
        H("Part IIUnitary Whole Graph Projective Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarywholegraphprojectiveproduct-actual-uniform-intrinsic-whole-graph-q-over-e-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.actual_uniform_intrinsic_whole_graph_q_over_e_product"),
                H("actual uniform intrinsic whole graph q over e product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual raw graph is absorbed into the genuine field component. No prescribed graph bit, divisor power, whole-SU target or global correction is discarded; the same uniform constants work for all graph tuples."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarywholegraphprojectiveproduct-actual-uniform-projective-whole-graph-q-over-e-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.actual_uniform_projective_whole_graph_q_over_e_product"),
                H("actual uniform projective whole graph q over e product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual center-quotient target is covered. The quotient action is constructed from the genuine SU action, and the quotient's surjectivity is proved library mathematics, rather than a bare-automorphism lift premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
