using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class Erdos203TorusFibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The torus is the square of the original common period. Its six-row subgroup is defined from the actual original equations.",
        H("Exact original-row restrictions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203torusfibers-torus"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203TorusFibers.Torus"),
                H("The full-period exponent torus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Torus is ZMod period times ZMod period."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203torusfibers-periodmap"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203TorusFibers.periodMap"),
                H("Simultaneous coordinate reduction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The additive homomorphism reduces both integer coordinates modulo the common original period."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203torusfibers-originalmap"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203TorusFibers.originalMap"),
                H("The unchanged original linear form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For row i, originalMap reduces the torus coordinates modulo its original modulus and evaluates a_i x + b_i y. The original modulus divides period."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203torusfibers-sixtorus"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203TorusFibers.sixTorus"),
                H("Common homogeneous kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The additive subgroup is the intersection of the kernels of the first six originalMap homomorphisms."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203torusfibers-integerform"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203TorusFibers.integerForm"),
                H("Integer linear form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The additive homomorphism on integer pairs evaluates a x + b y."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203torusfibers-0"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203TorusFibers.original_six_fibers"),
                H("Original modular fiber counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The restricted image has size e/g, with g the gcd of the original modulus and the two restricted coefficients. A translated original phase is compatible exactly when its residual value is divisible by g. Compatible fibers satisfy e times 8640 times their cardinality equals M squared times g; incompatible fibers are empty. No primitivity assumption is used."))),
                DescribeRole.Theorem)),
        []));
}
