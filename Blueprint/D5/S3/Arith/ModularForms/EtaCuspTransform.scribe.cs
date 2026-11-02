using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EtaCuspTransformDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/mathlib2026etacusps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant cusp multipliers with exact eta and reciprocal Euler normalization.",
        H("EtaCuspTransform"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partition-cusp-transform"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaCuspTransform.partition_cusp_transform"),
                H("Unshifted reciprocal partition transformation"),
                StatementSource.FromAuthor(Disp(Seq(Call("P", F.Id("q")), Sp, Eq, Sp, Zeta, Sp, Cdot, Sp, Call("sqrt", Div(Seq(Ell, F.Id("w")), Seq(D(2), Pi))), Sp, Cdot, Sp, Call("exp", Seq(Div(Pow(Pi, D(2)), Seq(D(6), Pow(Ell, D(2)), F.Id("w"))), Minus, Div(F.Id("w"), D(2,4)))), Sp, Cdot, Sp, Call("P", F.Id("u"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural l>0 and integers h,H with l dividing hH+1, one complex unit zeta works simultaneously for every complex w with Re(w)>0. Put q=exp(2*pi*i*h/l-w) and u=exp(2*pi*i*H/l-4*pi^2/(l^2*w)). Then P(q)=zeta sqrt(l*w/(2*pi)) exp(pi^2/(6*l^2*w)-w/24) P(u).")),
                    Paragraph(Text("E(q) is the infinite Euler product and P(q)=1/E(q). In eta coordinates P(exp(2*pi*i*tau))=exp(pi*i*tau/12)/eta(tau). The determinant-one cusp matrix has entries H,-b,l,-h, where hH+1=lb. Its eta constant xi gives zeta=xi sqrt(i) exp(pi*i*(h-H)/(12*l)). The principal-root identity sqrt(i*z)=sqrt(i)*sqrt(z) holds on the entire open right half-plane. No bound on Im(w), compact-domain assumption or transformation premise occurs in the final theorem. The helper eta normalization premise is discharged on the proof path."))),
                DescribeRole.Theorem))));

    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
