using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class PhysicalFixedNoiseInformationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-noise exponential-Gramian information expansion", H("Fixed-noise exponential-Gramian information expansion"), Blocks(
            Describe.Lean(DescribeId.Create("physical-fixed-noise-information"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PhysicalFixedNoiseInformation.physical_fixed_noise_information"),
                H("Fixed-noise exponential-Gramian information expansion"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let V be a finite-dimensional real inner-product space, W a complete real inner-product space, and B:V→V and C:V→W bounded linear maps. Zero-dimensional spaces and unobserved directions are allowed. Fix a positive prior precision beta and a positive coordinate-noise variance eta.")),
                    Paragraph(Text("Define H as the adjoint of C composed with C. Define G(T) as the actual Bochner integral from zero to T of the adjoint of C exp(t B) composed with C exp(t B). The determinant and trace are those of the finite-dimensional state operator, and the norm is the induced Hilbert operator norm.")),
                    Paragraph(Text("There are K at least zero and delta greater than zero such that for every positive T at most delta, the absolute difference between one half log det(id+(beta eta)^(-1)G(T)) and T trace(H)/(2 beta eta) is at most K T squared.")),
                    Paragraph(Text("Differentiability of the exponential integrand yields a uniform bound for G(T)-T H of order T squared. Positivity of G(T), its actual orthonormal eigenbasis, and a scalar logarithmic remainder bound control the determinant. An orthonormal trace estimate combines these errors.")),
                    Paragraph(Text("The result concerns the actual exponential-Gramian log determinant. In a finite-coordinate linear Gaussian observation model with state covariance beta^(-1)I, independent isotropic coordinate noise covariance eta I, and observation-coordinate Gramian G(T), this expression is mutual information in nats. Polynomial moment compression requires its own finite-time estimate."))), DescribeRole.Theorem))));
    private static Formula TheoremFormula()
    {
        Formula v = F.Id("V"), w = F.Id("W"), b = F.Id("B"), c = F.Id("C");
        Formula eta = new Formula.Symbol(FormulaIdentifier.Create("eta")), t = F.Id("t"), time = F.Id("T");
        Formula k = F.Id("K"), delta = DeltaLower, h = F.Id("H");
        Formula a = Call("A", t), g = Call("G", time);
        Formula exponent = Seq(Exp, Open, t, Sp, b, Close);
        Formula scale = Seq(Open, Beta, Sp, eta, Close, Caret, Grp(Minus, D(1)));
        Formula logdet = Call("det", Seq(Call("id", v), Plus, scale, Sp, g));
        Formula error = new Formula.Absolute(Seq(
            Frac, Grp(D(1)), Grp(D(2)), Sp, Log, Open, logdet, Close, Minus,
            Frac, Grp(time), Grp(D(2), Sp, Beta, Sp, eta), Sp, Call("tr", h)));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, v, Comma, Sp, w, Comma, Sp, b, Comma, Sp, c, Comma, Sp, Beta, Comma, Sp, eta, Comma,
            RowBreak, Grp(),
            Call("InnerProductSpace", Seq(Mathbb, Grp(F.Id("R"))), v), Sp, Land, Sp,
            Call("FiniteDimensional", Seq(Mathbb, Grp(F.Id("R"))), v), Sp, Land, Sp,
            Call("InnerProductSpace", Seq(Mathbb, Grp(F.Id("R"))), w), Sp, Land, Sp, Call("CompleteSpace", w), Comma,
            RowBreak, Grp(),
            b, Colon, Sp, new Formula.TypeArrow(v, v), Comma, Sp,
            c, Colon, Sp, new Formula.TypeArrow(v, w), Comma, Sp,
            Beta, Gt, D(0), Sp, Land, Sp, eta, Gt, D(0), Comma,
            RowBreak, Grp(),
            h, Eq, c, Caret, Grp(Star), Sp, c, Comma, Sp,
            a, Eq, c, Sp, exponent, Comma, Sp,
            g, Eq, Int, Underscore, Grp(D(0)), Caret, Grp(time),
            Sp, a, Caret, Grp(Star), Sp, a, Sp, F.Id("d"), t, Comma,
            RowBreak, Grp(),
            Exists, Sp, k, Comma, Sp, delta, Colon, Sp, k, Ge, D(0), Sp, Land, Sp, delta, Gt, D(0), Sp, Land, Sp,
            Forall, Sp, time, Comma, Sp, D(0), Lt, time, Le, delta, Sp, Rightarrow, Sp,
            error, Le, Sp, k, Sp, time, Caret, Grp(D(2)),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
