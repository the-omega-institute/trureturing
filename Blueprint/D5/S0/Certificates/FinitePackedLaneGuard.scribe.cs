using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FinitePackedLaneGuardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FinitePackedLaneGuard.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A packed guard proves every actual lane comparison",
        H("A packed guard proves every actual lane comparison"),
        Blocks(
            Paragraph(Text("Let B be 2 to the positive lane width and H be half of B. Exact equal-length operand lists encode X and Y. Each complete operand, including its full sum and offset, must be below H. These range bounds and the defined little-endian encoding remain proof obligations; native packing, lane counts and broadcast output are not trusted premises.")),
            Node("pack", "pack", "Encode the exact finite lane list",
                "Nat.ofDigits in base B retains every list position, including terminal zeros. Concrete applications must prove that these positions correspond to all original assignments and actual full bucket operands.", DescribeRole.Definition),
            Node("mask", "mask", "Mark the highest bit of every actual lane",
                "The mask encodes a list of H repeated exactly as many times as the operand length.", DescribeRole.Definition),
            Node("testBit-pack-lane", "testBit_pack_lane", "Extract a bounded lane's actual high bit",
                "Assume positive lane width, every complete list digit strictly below B, and an index strictly below the actual list length. Structural induction identifies the packed bit at width times index plus width minus one with that digit's high bit. Nat.testBit_two_pow_mul_add supplies the arithmetic bridge without replacing the original list length by a canonical digit length.", DescribeRole.Theorem),
            Node("guard-le", "guard_le", "Recover every pointwise inequality from the guard",
                "Assume positive width, exact equal operand lengths, both complete operands strictly below H at every occurrence, and the actual packed guard equality. Construct each digit z as H plus y minus x. Mathlib's digitwise addition theorem proves X plus packed z equals M plus Y, so the natural subtraction is exactly packed z. Each z is below B. The guard forces its highest bit at every actual list index; Nat.ge_two_pow_of_testBit yields H at most z and hence x at most y. List.Forall₂ retains every occurrence. Only guard-to-comparison soundness is claimed.", DescribeRole.Theorem),
            Paragraph(Text("An EJM bucket consumer must prove exact packing and broadcast maps from every original four-valued assignment to these lists, bounds on the complete shifted bucket operands, the actual guard equality, and the integer shift restoration. First-freeze admission requires a real consumer with all concrete premises kernel checked. This conditional guard theorem supplies no complete EJM certificate acceptance or frontier coverage. Source-owned Reg evidence and current bindings remain unfinished under https://github.com/the-omega-institute/trureturing/issues/16309.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
