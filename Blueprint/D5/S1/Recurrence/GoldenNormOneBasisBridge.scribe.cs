using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenNormOneBasisBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GoldenNormOneBasisBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even golden power and its norm-one companion have an explicit intertwiner. "
            + "Its Fibonacci determinant identifies precisely the excluded basis primes.",
        H("Golden Power and Integral Basis Transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-norm-one-intertwiner"),
                DeclarationHandle.Create(Prefix + "norm_one_intertwining"),
                H("The matrix relation holds before discarding bad primes"),
                StatementSource.FromAuthor(Call("Implies", Call("NormOne", F.Id("a"), F.Id("b")),
                    Call("Eq", Call("mul", F.Id("R"), F.Id("P")), Call("mul", F.Id("P"), F.Id("C"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Over every commutative ring, R=[[a+b,b],[b,a]], "
                        + "P=[[b,0],[a,-1]] and C=[[2a+b,-1],[1,0]]. The hypothesis "
                        + "a^2+a*b-b^2=1 is the actual golden norm-one equation. "
                        + "The theorem proves R*P=P*C and basis_determinant proves det(P)=-b.")),
                    Paragraph(Text("goldenAction_mulVec binds R to multiplication by the "
                        + "original GoldenInt, using coordinate order (b,a). No new "
                        + "quadratic carrier or assumed dynamical equivalence is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-even-return-transfer"),
                DeclarationHandle.Create(Prefix + "even_golden_returns_iff"),
                H("Return times transfer only with an invertible basis coefficient"),
                StatementSource.FromAuthor(Call("Implies", Call("IsUnit", F.Id("b")),
                    Call("Iff", Call("Return", F.Id("goldenAction"), F.Id("t")),
                        Call("Return", F.Id("companion"), F.Id("t"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every even depth 2*k and modulus m, b is the "
                        + "actual second coordinate of phi^(2*k), equal to F(2*k). "
                        + "When its residue is a unit, the golden action and the "
                        + "existing Lucas companion with parameter L(2*k) have "
                        + "identical return times at every natural t. An explicit "
                        + "two-sided inverse proves this; determinant nonvanishing "
                        + "is not silently inferred in a composite residue ring.")),
                    Paragraph(Text("At depth eight, b=21 and L(8)=47. The change of "
                        + "basis excludes moduli sharing a factor with 21. In particular "
                        + "the fixed-point tower at prime three in the companion "
                        + "does not transfer to the original golden action. This "
                        + "prevents reporting an ordinary recurrence fixed point "
                        + "as a classical Wall-Sun-Sun witness."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(xs[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
