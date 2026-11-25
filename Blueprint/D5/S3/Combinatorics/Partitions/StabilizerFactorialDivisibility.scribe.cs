using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class StabilizerFactorialDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/StabilizerFactorialDivisibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial divisibility for the masses of a labeled partition.",
        H("Scaled block masses and stabilizer orders"),
        Blocks(Describe.Lean(
            DescribeId.Create("factorial-product-divides-scaled-coordinate"),
            DeclarationHandle.Create(Prefix + "factorial_product_dvd_scaled_coordinate"),
            H("The block factorial product divides each scaled mass"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let I be a finite set and k a natural number. The natural size family s "
                    + "has sum k and the natural value family v assigns a value to each block. Mass(s,v) "
                    + "is the sum of the products s(i)v(i), and BlockFactorials(s) is the product of "
                    + "the factorials of the sizes. SizeSum(s) is the sum of the block sizes. If Mass(s,v) is divisible by k minus one, "
                    + "then BlockFactorials(s) divides each block mass multiplied by the factorial of k minus two.")),
                Paragraph(Text(
                    "For zero or one label the factorial product is one. For at least two labels, remove one element from the designated block and denote the new sizes by b. "
                    + "Write P for their factorial product. Multinomial integrality gives that P divides "
                    + "the factorial of k minus one. Removing one element from any nonempty block of b "
                    + "gives that P divides the factorial of k minus two times that block's size. "
                    + "Multiply by the block values and sum. Subtraction from the scaled total "
                    + "shows that P divides the scaled value of the original designated block. "
                    + "Multiplying by the original block size restores the full factorial product.")),
                Paragraph(Text(
                    "The divisibility hypothesis is necessary for uniform coverage at a fixed positive total "
                    + "when k is at least two. Use block sizes k minus one and one, with values zero and m. "
                    + "The singleton demand is m divided by k minus one.")),
                Paragraph(Text(
                    "For equal-coordinate groups of a probability profile, the factorial product is the "
                    + "order of the profile stabilizer. In a regular seed orbit, a stabilizer orbit assigned "
                    + "to a label group of size s(i) contributes the stabilizer order divided by s(i) "
                    + "to each label in the group. The divisibility theorem makes the corresponding block "
                    + "demands integers when the masses are scaled by the factorial of k minus two."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        Formula s = F.Id("s");
        Formula v = F.Id("v");
        Formula totalDivisor = Seq(k, Sp, Minus, Sp, D(1));
        Formula individual = Seq(Call("factorial", Seq(k, Sp, Minus, Sp, D(2))),
            Sp, Cdot, Sp, Call("s", i), Sp, Cdot, Sp, Call("v", i));
        return Disp(Seq(Forall, Sp, F.Id("I"), Sp, k, Sp, s, Sp, v, Comma, Sp,
            Call("SizeSum", s), Sp, Eq, Sp, k,
            Sp, Land, Sp, Call("Divides", totalDivisor, Call("Mass", s, v)), Sp, Rightarrow,
            Sp, Forall, Sp, i, Comma, Sp,
            Call("Divides", Call("BlockFactorials", s), individual)));
    }
}
