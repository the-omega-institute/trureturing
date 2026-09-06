using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilArchimedeanHighModeBoundsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilArchimedeanHighModeBounds.";
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
        Formula c = F.Id("c"), n = F.Id("n"), L = F.Id("L");
        Formula pi = F.Id("pi"), w = F.Id("omega"), R = F.Id("R");
        Formula absn = Call("abs", n);
        Formula symbolBound = Seq(D(1), Plus,
            Call("div", L, Call("mul", D(2), pi, absn)));
        Formula diagonalBound = Seq(
            Call("div", D(1), Call("mul", pi, absn)), Plus,
            Call("div", L, Call("mul", D(2), Call("square", pi), Call("square", n))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The actual Gamma symbol and diagonal correction have frequency-decaying "
                + "bounds, supplying the constants for energy-weighted Weil elimination.",
            H("Weil Archimedean High-Mode Bounds"),
            Blocks(
                Paragraph(Text(
                    "Use the existing arithmeticBoundarySymbol s(c,n), with c a natural "
                    + "number at least 2, L=log(c), omega=2*pi*n/L and integer n nonzero. "
                    + "Write beta_j=2*j+1/2 and R_j=(1-exp(-beta_j*L)) "
                    + "*(beta_j^2-omega^2)/(beta_j^2+omega^2)^2. "
                    + "GammaPart means s(c,n) plus its explicit pole and finite prime "
                    + "terms, so it is exactly the negative Gamma series already in the "
                    + "canonical arithmetic symbol. There is no second Weil definition.")),
                Describe.Lean(
                    DescribeId.Create("arithmetic-archimedean-high-mode-bounds"),
                    DeclarationHandle.Create(Owner + "arithmetic_archimedean_high_mode_bounds"),
                    H("Frequency-sensitive arithmetic Gamma bounds"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("And", Call("AtLeast", c, D(2)), Call("Nonzero", n)),
                        Rightarrow,
                        Call("And",
                            Call("LessEqual", Call("abs", Call("GammaPart", c, n)), symbolBound),
                            Call("SummableNorm", R),
                            Call("LessEqual", Call("abs", Call("mul", Call("div", D(2), L),
                                Call("tsum", R))), diagonalBound))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "A positive telescoping estimate for j>=1 bounds the majorant "
                            + "sum omega/(beta_j^2+omega^2) by omega/(omega+1/2). The zeroth "
                            + "term is at most 1/omega. Hence the complete majorant is "
                            + "at most 1+1/omega. Its bounded nonnegative partial sums also "
                            + "prove convergence. The actual sine series is dominated "
                            + "termwise because 0<=1-exp(-beta_j*L)<=1.")),
                        Paragraph(Text(
                            "For the correction use |beta_j^2-omega^2|<=beta_j^2+omega^2. "
                            + "Its absolute series is dominated by the same summable "
                            + "majorant divided by |omega|. Multiplication by 2/L and "
                            + "|omega|=2*pi*|n|/L gives the displayed diagonal error. "
                            + "Absolute summability is proved, so totalized divergent "
                            + "series cannot make either bound vacuous.")),
                        Paragraph(Text(
                            "The same-source Fourier calculation identifies this series "
                            + "as the actual Gamma diagonal correction. Combining the "
                            + "new symbol bound with the classical integer discrete-Hilbert "
                            + "norm at most pi controls every off-diagonal mode. The "
                            + "resulting simultaneous logarithmic form lower bound, "
                            + "weighted Schur completion and executed c=3 interval "
                            + "certificate are proved separately in the existing RH "
                            + "theory volume. They are not conclusions of this Lean "
                            + "declaration. Lean and Scribe compilation were not run "
                            + "in this research session."))),
                    DescribeRole.Theorem))));
    }
}
