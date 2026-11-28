using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class CosineJetHankelCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cosine coordinate and its first scale derivative jointly detect the critical line in a finite nonreal spectrum.",
        H("Cosine and Scale-Jet Hankel Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("paired-cosine-jet-hankel-critical-or-real"),
            DeclarationHandle.Create("D5/S3/Weil/GoldenCriticalSpectrum/CosineJetHankelCriterion.cosine_jet_hankel_iff_critical_or_real"),
            H("Paired moment positivity removes even-sampling aliases"),
            StatementSource.FromAuthor(Criterion()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For any natural d, let rho enumerate d complex points, allowing repetitions, and suppose its finite support is closed under conjugation. "
                    + "Let t be any nonzero real number. Write Gamma(rho)=-i(rho-1/2), C(z)=2 cos(z), and J(z)=d/du C(uz) at u=1, so J(z)=-2z sin(z). "
                    + "H(t,rho) is the normalized d by d Newton-Hankel matrix of the nodes C(t Gamma(rho(j))); K(t,rho) uses J(t Gamma(rho(j))) instead. "
                    + "ConjugationStable in the formula means closure of the finite support, and PSD means positive semidefinite. No equality of conjugate multiplicities is required.")),
                Paragraph(Text(
                    "For z=x+iy, put A=Im C(z) and B=Im J(z). The estimate 4 x^2 y^2 <= (x^2+1+cosh(y)^2)(A^2+B^2) implies that both coordinates are real exactly when z lies on one of the two axes. "
                    + "To obtain the estimate when y is nonzero, set r=y cosh(y)/sinh(y). Then |r|<=cosh(y), while x^2 A^2+(B-rA)^2=4x^2 sinh(y)^2. "
                    + "Two-dimensional Cauchy-Schwarz and |y|<=|sinh(y)| give the bound. The case y=0 follows directly.")),
                Paragraph(Text(
                    "Both node lists have conjugation-stable support because C and J are even and commute with conjugation. The Newton-Hankel real-root criterion therefore applies to each list. "
                    + "Since t is nonzero, the two-axis alternative for t Gamma(rho(j)) is exactly Re rho(j)=1/2 or Im rho(j)=0. "
                    + "For a spectrum without real points this is critical-line location. A single cosine list can hide off-critical points whenever its real phase is an integer multiple of pi; the derivative list detects those points.")),
                Paragraph(Text(
                    "At the golden sampling period the same criterion applies without requiring a second irrational scale. This is a finite moment criterion. "
                    + "The entries of K are moments of J itself. A single scale derivative of H gives mixed moments instead, and does not supply K; realizing powers of J can require higher derivative data. "
                    + "Realization by common smooth Weil tests and control of the complete zero-sum complement are additional requirements; the criterion asserts neither complete Weil positivity nor an independent proof of RH."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);

    private static Formula Criterion()
    {
        Formula d = F.Id("d"), rho = F.Id("rho"), t = F.Id("t"), j = F.Id("j");
        Formula nats = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula fin = Call("Fin", d);
        Formula point = Call("rho", j);
        Formula axes = Seq(Call("Re", point), Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(2)),
            Sp, Lor, Sp, Call("Im", point), Sp, Eq, Sp, D(0));
        Formula matrices = Seq(Call("PSD", Call("H", t, rho)), Sp, Land, Sp,
            Call("PSD", Call("K", t, rho)));
        return Disp(All("d", nats, All("rho", Seq(fin, Sp, To, Sp, complexes),
            All("t", reals, Seq(Open, t, Sp, Neq, Sp, D(0), Sp, Land, Sp,
                Call("ConjugationStable", rho), Close, Sp, Implies, Sp,
                Open, Open, matrices, Close, Sp, Iff, Sp, All("j", fin, axes), Close)))));
    }
}
