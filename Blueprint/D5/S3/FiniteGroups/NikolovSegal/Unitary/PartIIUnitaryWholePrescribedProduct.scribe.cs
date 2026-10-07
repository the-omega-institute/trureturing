using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryWholePrescribedProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive q there are single constants N(q),C(q), chosen before all finite fields and ranks n>=6 above the field-cardinality cutoff. Arbitrary genuine compatible diagonal similitude and field-action tuples and positive divisors e(j)|q retain the original q/e(j). One actual SU correction tuple y is chosen before every actual whole-SU target b; x may depend on b. Each ordered value is x(j) inverse times ((alpha(j)*MulAut.conj(y(j) inverse)) to the q/e(j) power) applied to x(j). The genuinely proved K5 width closes whole-group coverage without a supplied decomposition premise.",
        H("Part IIUnitary Whole Prescribed Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarywholeprescribedproduct-actual-uniform-intrinsic-whole-q-over-e-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholePrescribedProduct.actual_uniform_intrinsic_whole_q_over_e_product"),
                H("actual uniform intrinsic whole q over e product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The separately proved absolute whole-SU width is genuinely consumed. There is no factorization, scalar-coverage or action-existence premise. This endpoint covers prescribed genuine D/Phi actions; recognition of arbitrary bare SU automorphisms remains a separate mathematical leaf."))),
                DescribeRole.Theorem),
            Paragraph(Text("These parameterized results and their consumed helpers support proofs about actual matrix groups over finite fields. Every displayed Lean statement retains its original hypotheses. This package contains no finite enumeration or benchmark-instance deposit. The source geometry is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239. The proof implementation is repository-derived and no originality claim is made. Bare arbitrary automorphism classification, small-field/tiny-rank coverage for the prescribed products, all-family exhaustion and strong completeness are separate obligations. Escape registration is unfinished under CLAUDE3.9 and issue12291; this is not declared_validated registration.")))));
}
