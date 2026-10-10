using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class PrimeTripletWheelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection preserves the cardinality of the two oriented wheel candidate spaces at every nonzero modulus.",
        H("Prime Triplet Wheel Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wheel-reflect-involutive"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeTripletWheel.reflect_involutive"),
                H("The affine wheel reflection is an involution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonzero modulus W, the map a ↦ -a-6 on ZMod W "
                    + "is its own inverse. This is the transport map between the two "
                    + "orientation charts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wheel-plus-reflect-iff"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeTripletWheel.plus_reflect_iff"),
                H("Reflection exchanges wheel admissibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A residue is admissible for {0,2,6} exactly when its reflected "
                    + "residue is admissible for {0,4,6}. The proof uses only that "
                    + "negation preserves units and that the three offsets are paired "
                    + "by the affine reflection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wheel-reflect-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeTripletWheel.reflectEquiv"),
                H("The two candidate spaces are equivalent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The subtype of H-plus wheel candidates and the subtype of H-minus "
                    + "wheel candidates are equivalent finite spaces. This packages the "
                    + "orientation symmetry before any choice of origin or observation chart."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("wheel-candidate-space-card"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeTripletWheel.candidate_space_card_eq"),
                H("Oriented candidate spaces have equal cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonzero modulus, the two oriented wheel candidate spaces "
                    + "have equal cardinality. The statement locally supplies Fintype.ofFinite "
                    + "instances for both residue subtypes; its only hypothesis is NeZero W. "
                    + "This is a general density-symmetry theorem "
                    + "for finite wheel candidates; it makes no claim about infinitude, "
                    + "asymptotics, or the actual distribution of prime triplets."))),
                DescribeRole.Theorem))));
}
