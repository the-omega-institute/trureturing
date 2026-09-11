using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class BaezDuarteNewtonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Baez-Duarte Newton series converges to reciprocal zeta for every complex "
        + "argument with real part greater than one, with absolute interchange derived on that domain.",
        H("Baez-Duarte Newton Reciprocal Zeta"),
        Blocks(Describe.Lean(
            DescribeId.Create("newton-has-sum"),
            DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteNewton.baez_duarte_newton_hasSum"),
            H("The original Newton series on the initial half-plane"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
            Blocks(
                Paragraph(Text("Here c is the existing real baezDuarte finite binomial transform "
                    + "of reciprocals of real parts of zeta at the positive even integers, cast "
                    + "to the complex numbers. P is the existing normalizedPochhammer polynomial: "
                    + "the product of the factors one minus z divided by r for r from one to k. "
                    + "The conclusion is HasSum at the complex reciprocal of riemannZeta s. "
                    + "The only analytic hypothesis is that the real part of s exceeds one.")),
                Paragraph(Text("For m=n+1, the unsigned coupled kernel is the reciprocal square "
                    + "of m times the k-th power of one minus that reciprocal square, times "
                    + "the norm of P(k,s/2). Its row sums are Q(k) times that norm. The imported "
                    + "Q and P bounds yield an outer power exponent minus (Re(s)+1)/2, strictly "
                    + "below minus one. Eventual comparison retains the finite prefix, including "
                    + "k=0. The bound on the absolute Moebius function then proves absolute "
                    + "summability of the signed coupled series before Fubini is applied.")),
                Paragraph(Text("The imported signed coefficient HasSum evaluates one family of "
                    + "fibers. A private adapter of mathlib's complex binomial series evaluates "
                    + "the other, and positive-real-base power rules identify the resulting "
                    + "Moebius Dirichlet terms. The existing Dirichlet product and nonvanishing "
                    + "theorems identify their sum with reciprocal zeta. Both zero indices are "
                    + "retained; at n=0 the inner series sums to one, and at s=2 only c(0) survives.")),
                Paragraph(Text("This is a repo-derived formal proof of the source's initial "
                    + "half-plane identification, not its sharper half-plane extension or an RH "
                    + "direction. The generic adapters are private. Utility none classifies this "
                    + "as a general infinite analytical theorem, not a finite computation."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement()
    {
        Formula s = FormulaDsl.Id("s"), k = FormulaDsl.Id("k");
        Formula complex = Seq(Mathbb, Grp(FormulaDsl.Id("C")));
        Formula nat = Seq(Mathbb, Grp(FormulaDsl.Id("N")));
        Formula term = Seq(Call("c", k), Sp, Call("P", k, new Formula.Fraction(s, D(2))));
        Formula series = Call("HasSum", Seq(Open, k, Colon, nat, Close, Mapsto, term),
            new Formula.Fraction(D(1), Call("riemannZeta", s)));
        return Disp(Seq(Forall, Sp, s, InMacro, complex, Comma, Sp,
            D(1), Lt, Call("Re", s), Rightarrow, Sp, series));
    }
}
