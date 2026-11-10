using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PowerSeries;

internal sealed class DottieInverseSeriesDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational arcsine coefficients specify a unique formal inverse; analytic endpoint convergence is a further obligation.",
        H("The prescribed rational inverse series"),
        Blocks(
            Describe.Lean(DescribeId.Create("dottie-arcsine-coefficients"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.alpha"),
                H("Rational coefficients in every degree"),
                StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), Seq(
                    Call("alpha", Seq(D(2), F.Id("n"))), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Call("alpha", Seq(D(2), F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp,
                    Call("div", Call("choose", Seq(D(2), F.Id("n")), F.Id("n")),
                        Seq(D(4), Caret, Grp(F.Id("n")), Open,
                            D(2), F.Id("n"), Sp, Plus, Sp, D(1), Close)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient sequence alpha takes values in the rationals. Its even coefficients vanish and its degree 2n+1 coefficient is choose(2n,n)/(4^n(2n+1)). The definition selects these cases using the parity and integer half of the input degree."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-arcsine-series"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.arcsine"),
                H("The formal rational arcsine series"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("S"), Sp, Eq, Sp,
                    Call("mk", Call("alpha"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S denotes PowerSeries.mk alpha over the rationals. Its coefficient in degree zero is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-forward-series"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.forward"),
                H("The forward series"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("A"), Sp, Eq, Sp,
                    D(2), F.Id("X"), Sp, Plus, Sp, D(2), F.Id("S")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A is the literal rational formal series 2X+2S. Its constant coefficient is zero and its linear coefficient is 4, a unit in the rational field."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-prescribed-inverse"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.inverse"),
                H("The prescribed formal inverse"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("B"), Sp, Eq, Sp,
                    Call("substInvOfIsUnit", F.Id("A"), Call("unit", D(4)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B is exactly A.substInvOfIsUnit for the proof that the linear coefficient 4 is a unit. The choice of that proof does not alter the formal series."))),
                DescribeRole.Definition),
            new DocumentBlock.Section(H("Connecting an analytic inverse"), Blocks(
                Paragraph(Text("For a complex function H analytic at zero and real on the real axis near zero, let h(y)=Re(H(y)) for real y. The real_taylor_data lemma supplies real analyticity of h and the real and imaginary parts of every complex derivative coefficient, including degree zero. Its Taylor series T has coefficient iteratedDeriv(n,h,0)/n!.")),
                Paragraph(Text("Suppose H(0)=0, the real function a(x)=2x+2arcsin(x) has the expansion given by A mapped to the reals, and a(h(y))=y near zero. Then T has zero constant coefficient. The scalar composition correspondence identifies the expansion of a composed with h with the realization of A substituted by T. Uniqueness of one-dimensional analytic expansions makes that substitution equal X. The mapped rational series B is another right formal inverse, by map_subst. Formal inverse uniqueness therefore gives T equal to B mapped to the reals. The same real_taylor_data coefficients then identify every complex derivative coefficient of H with the complex image of the corresponding rational coefficient of B.")),
                Paragraph(Text("These local analytic and inverse-germ premises require proof for a selected H. A common analytic inverse on a disk of radius greater than pi, real preservation, the exact arcsine germ, and its selected value at pi remain necessary to establish absolute summability at pi and identify its sum. No endpoint convergence or cosine fixed-point value is asserted here.")))))));
}
