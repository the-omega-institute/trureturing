using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class IntegerCodeArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen signed-magnitude HF integer encoding carries the transported ordered ring arithmetic.",
        H("Arithmetic and Order on Integer HF Codes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-ring-equiv"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_ring_equiv"),
                H("Integer arithmetic on the literal codes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib Equiv.commRing and Equiv.ringEquiv transport the integer ring to exactly the "
                    + "structural signed-magnitude HF subtype. The forward function is the frozen decodeInt, and "
                    + "the inverse is the frozen int_code_equiv encoder."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-order-iso"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_order_iso"),
                H("Integer order through the same functions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib Equiv.linearOrder transports order and maximum through the same frozen "
                    + "equivalence. The OrderIso has the same decoder and encoder as the RingEquiv; it introduces "
                    + "no alternative coding."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-zero"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_zero"),
                H("Encoding zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original integer encoder sends zero to the zero of the transported code ring."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-zero"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_zero"),
                H("Decoding zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original decoder sends the zero code of the transported ring to integer zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-one"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_one"),
                H("Encoding one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original integer encoder sends one to the unit of the transported code ring."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-one"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_one"),
                H("Decoding one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original decoder sends the unit code of the transported ring to integer one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-add"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_add"),
                H("Encoding addition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all integers, encoding their sum equals the sum of their literal HF codes. This is an "
                    + "application of the inverse RingEquiv addition law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-add"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_add"),
                H("Decoding addition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all legal integer codes, the original decoder of their code-ring sum equals the sum of "
                    + "their decoded integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-mul"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_mul"),
                H("Encoding multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all integers, encoding their product equals the product of their codes in the "
                    + "transported ring."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-mul"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_mul"),
                H("Decoding multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all legal codes, decoding the transported product equals multiplying the decoded "
                    + "integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-neg"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_neg"),
                H("Encoding negation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every integer, its encoded negative is the additive inverse of its code."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-neg"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_neg"),
                H("Decoding negation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every legal code, decoding its additive inverse gives the negative of its decoded "
                    + "integer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-sub"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_sub"),
                H("Encoding subtraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all integers, the original encoder preserves subtraction in the transported code ring."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-sub"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_sub"),
                H("Decoding subtraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all legal codes, the original decoder preserves subtraction into ordinary integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-le"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_le"),
                H("Encoding non-strict order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all integers, comparison of their codes is equivalent to comparison of the original "
                    + "integers. The inverse OrderIso supplies both directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-le"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_le"),
                H("Decoding non-strict order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all legal codes, comparison of the decoded integers is equivalent to comparison in the "
                    + "transported code order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-lt"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_lt"),
                H("Encoding strict order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all integers, strict comparison of their codes is equivalent to strict comparison of "
                    + "the original integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-lt"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_lt"),
                H("Decoding strict order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all legal codes, strict comparison of the decoded integers is equivalent to strict "
                    + "comparison in the code order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-max"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_max"),
                H("Encoding maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all integers, encoding their maximum gives the maximum of their codes. This follows "
                    + "from monotonicity of the inverse OrderIso."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-max"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_max"),
                H("Decoding maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all legal codes, decoding their maximum gives the maximum of their decoded integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-ordered-ring-compatibility"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.instIsStrictOrderedRing"),
                H("Order and ring arithmetic are compatible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's generic ordered-ring pullback consumes the proved decoding laws for zero, "
                    + "one, addition, multiplication and both comparisons. It supplies the ordered-ring "
                    + "instance on the same subtype without assuming compatibility as a new field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-encode-max-add-one"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_max_add_one"),
                H("Encoding the generated-event time expression"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The universal addition, maximum and unit laws prove that encoding maximum parent time plus "
                    + "one equals maximum encoded parent time plus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-arithmetic-decode-max-add-one"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_max_add_one"),
                H("Decoding the generated-event time expression"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Decoding maximum code parent time plus one gives the maximum of the original decoded times "
                    + "plus one. These are arithmetic representation laws; internal ZFC ContextGraph and "
                    + "OperationGraph realization obligations remain for later work."))),
                DescribeRole.Theorem))));
}
