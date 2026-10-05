using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParityCompositionKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParityCompositionKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform weak compositions and a biased Bernoulli vector give two laws on the same terminal parity fiber.",
        H("Parity Composition Kernels"),
        Blocks(
            Describe.Lean(DescribeId.Create("parity-composition-actual"),
                DeclarationHandle.Create(Prefix + "R"), H("Composition parity mass"),
                StatementSource.FromAuthor(Disp(Seq(Call("R", F.Id("d"), F.Id("M"), F.Xi), Sp, Eq, Sp,
                    Ratio(Call("choose", Seq(Open, F.Id("M"), Minus, F.Id("h"), Close, Slash, D(2), Plus,
                        F.Id("d"), Minus, D(1)), Seq(F.Id("d"), Minus, D(1))),
                        Call("choose", Seq(F.Id("M"), Plus, F.Id("d"), Minus, D(1)),
                            Seq(F.Id("d"), Minus, D(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here d and M are natural numbers, xi : Fin d -> Bool, and h is the sum of the Boolean digits. "
                    + "The displayed formula applies when h <= M and h mod 2 = M mod 2; the mass is zero otherwise. "
                    + "The numerator counts the weak compositions after subtracting the parity vector and dividing each part by two."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("parity-composition-reference"),
                DeclarationHandle.Create(Prefix + "Q"), H("Conditioned Bernoulli mass"),
                StatementSource.FromAuthor(Disp(Seq(Call("Q", F.Id("d"), F.Id("M"), F.Xi), Sp, Eq, Sp,
                    Ratio(Seq(Power(F.Nu, F.Id("h")), Power(Seq(Open, D(1), Minus, F.Nu, Close),
                        Seq(F.Id("d"), Minus, F.Id("h")))), Index(F.Id("p"), F.Id("e")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameter nu is M/(2M+d), eta is d/(2M+d), and p_e is (1+(-1)^M eta^d)/2. "
                    + "The displayed formula applies when h mod 2 = M mod 2; the mass is zero otherwise. "
                    + "For positive d and M, this is the law of independent Bernoulli(nu) bits conditioned on the terminal parity. "
                    + "The conditioned bits are not asserted to be independent."))),
                DescribeRole.Definition))));
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Power(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Index(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
}

