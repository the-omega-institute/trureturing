using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilArithmeticCouplingSecondJetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingSecondJet.";

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq(result.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), N = F.Id("N"), m = F.Id("m"), v = F.Id("v");
        Formula budget = Call("B_arith", c);
        Formula rhs = Seq(
            Frac(Seq(D(2), Sp, budget, Sp, Pow(N, D(2))),
                Seq(Pi, Sp, Pow(Call("abs", m), D(2)), Sp,
                    Grp(Call("abs", m), Minus, N))),
            Sp, Call("l1", v));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The concrete prime-pole-Gamma divided-difference column has a second exterior "
                + "jet whose remainder gains an additional N/|m| factor.",
            H("Weil Arithmetic Coupling Second Jet"),
            Blocks(
                Paragraph(Text(
                    "The source imports the already bounded arithmetic boundary symbol from "
                    + "WeilArithmeticCouplingJet. It keeps the zeroth and first powers of the "
                    + "interior Fourier index in the exact expansion of 1/(m-n). No replacement "
                    + "of the prime or Gamma terms by an asymptotic model is made.")),
                Describe.Lean(
                    DescribeId.Create("arithmetic-coupling-second-jet-error"),
                    DeclarationHandle.Create(Owner + "arithmetic_coupling_second_jet_error"),
                    H("Second exterior jet for the actual arithmetic coupling"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("interiorBand", N), Land, Call("outside", m, N),
                        Rightarrow,
                        Call("norm", Seq(Call("column", c, v, m), Minus,
                            Call("secondJet", c, v, m))),
                        Leq, rhs))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact scalar identity is 1/(m-n)=1/m+n/m^2+"
                        + "n^2/(m^2(m-n)). The previously proved uniform arithmetic boundary "
                        + "budget bounds the last numerator. For |n|<=N<|m| this gives a "
                        + "pointwise remainder proportional to N^2/(|m|^2(|m|-N)). After "
                        + "square summation over |m|>M, the remainder therefore improves by "
                        + "order (N/M)^2 relative to the first jet. The infinite low-rank Gram "
                        + "assembly is deliberately left to the arithmetic certificate rather "
                        + "than asserted as part of this pointwise theorem."))),
                    DescribeRole.Theorem))));
    }
}
