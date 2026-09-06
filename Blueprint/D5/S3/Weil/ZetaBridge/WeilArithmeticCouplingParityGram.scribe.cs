using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilArithmeticCouplingParityGramDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram.";
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), m = F.Id("m"), n = F.Id("n");
        Formula S = F.Id("S"), v = F.Id("v");
        Formula s = Call("s", c, n);
        Formula jp = Call("J2", c, S, v, m);
        Formula jm = Call("J2", c, S, v, Seq(Minus, m));
        Formula rhs = Seq(Call("div", D(2),
            Seq(Call("square", F.Id("pi")), Sp, Call("square", m))), Sp,
            Grp(Call("normSq", Call("U", m)), Plus,
                Call("normSq", Call("V", m))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The concrete arithmetic symbol is odd; reflection pairing retains "
                + "four boundary moments in two positive moment Gram blocks.",
            H("Weil Arithmetic Coupling Parity Gram"),
            Blocks(
                Paragraph(Text(
                    "s(c,n) is exactly arithmeticBoundarySymbol from WeilArithmeticCouplingJet, "
                    + "including the pole, infinite Gamma series and finite von Mangoldt sine sum. "
                    + "J2 is exactly couplingSecondJet from WeilArithmeticCouplingSecondJet. "
                    + "Neither the Weil form nor its Fourier normalization is redefined.")),
                Describe.Lean(
                    DescribeId.Create("arithmetic-boundary-symbol-neg"),
                    DeclarationHandle.Create(Owner + "arithmetic_boundary_symbol_neg"),
                    H("Reflection of the actual arithmetic symbol"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("s", c, Seq(Minus, n)), Eq, Minus, s))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The identity holds for every natural c and integer n. The arithmetic "
                        + "application uses c>=2, where the imported source independently proves "
                        + "absolute convergence. Each pole and Gamma numerator is odd in the "
                        + "Fourier frequency and its denominator is even; the finite prime "
                        + "sum is odd by the sine identity. Oddness is proved rather than assumed."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("arithmetic-second-jet-pair-energy"),
                    DeclarationHandle.Create(Owner + "arithmetic_second_jet_pair_energy"),
                    H("Exact paired second-jet energy"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Nonzero", m), Rightarrow,
                        Call("normSq", jp), Plus, Call("normSq", jm), Eq, rhs))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "S is any finite integer set and v is any complex coefficient family. "
                        + "A0=sum v_n, B0=sum s_n*v_n, A1=sum n*v_n, B1=sum n*s_n*v_n. "
                        + "U_m=-s_m*A0+B1/m and V_m=B0-s_m*A1/m. The collected jets are "
                        + "J2(m)=(U_m+V_m)/(pi*m) and J2(-m)=(U_m-V_m)/(pi*m). "
                        + "The complex parallelogram identity proves the displayed result. "
                        + "No coefficient parity, reality or boundary-moment cancellation is assumed. "
                        + "Summing over positive exterior indices gives two positive 2-by-2 "
                        + "moment Gram blocks. The infinite summation, its scalar remainder, "
                        + "the executable c=3 enclosure certificate and the Fourier/domain "
                        + "identification are separate paper/computer-assisted steps in the "
                        + "existing RH theory volume. This declaration does not prove an "
                        + "unbounded-scale Xi limit."))),
                    DescribeRole.Theorem))));
    }
}
