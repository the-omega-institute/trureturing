using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DerivativeLayerNativeGramianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invertible physical scaling and native Gramian limit", H("Invertible physical scaling and native Gramian limit"), Blocks(
            Describe.Lean(DescribeId.Create("derivative-layer-native-gramian"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian"),
                H("Invertible physical scaling and native Gramian limit"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let V be an arbitrary finite-dimensional real inner-product space, and W an arbitrary complete real inner-product space. Let B:V→V and C:V→W be arbitrary linear maps. Neither observability of the whole V nor a positive dimension is assumed.")),
                    Paragraph(Text("Put n=dim V, N(j)=the intersection of ker(C B^k) for 0≤k<j, U=N(n) orthogonal complement, E(j)=N(j) intersect N(j+1) orthogonal complement for 0≤j<n. Pi(j):V→V is the actual orthogonal projection onto E(j). All n layer indices are retained, even when their layer is zero. Write b and c for the continuous linear maps associated to B and C; i:U→V is the inclusion. All norms are induced Hilbert operator norms.")),
                    Paragraph(Text("On U let Q(j) be Pi(j) restricted to U, with its range returned to U by the orthogonal projection onto U. Put d(T)=sum sqrt(T) T^j Q(j) and e(T)=sum (sqrt(T) T^j)^(-1) Q(j). Define A(t)=c exp(t b) i and G(T)=the interval integral from zero to T of A(t) adjoint composed with A(t).")),
                    Paragraph(Text("Put P(s)=sum over j<n of s^j/j! c b^j Pi(j) i and H=the interval integral from zero to one of P(s) adjoint composed with P(s). Write Z(T,s)=sqrt(T) A(T s) e(T). Composition is written by juxtaposition in the display, and a star denotes the Hilbert adjoint.")),
                    Paragraph(Text("For every T>0, d(T)e(T) and e(T)d(T) both equal the identity on U, and e(T)G(T)e(T) equals the integral of Z(T,s) adjoint composed with Z(T,s). H has positive quadratic form at every nonzero state. There is R≥0 for which the linear error holds whenever 0<T≤1 and T times the norm of b is less than one.")),
                    Paragraph(Text("Projection orthogonality gives the inverse equations without a rank premise. The physical change of variables t=T s and self-adjointness of the scaling give the integral identity. Uniform normalized-trajectory convergence controls the difference of the two squared operators and its integral.")),
                    Paragraph(Text("The finite derivative filtration supplies orthogonal geometry, while the exponential power series and Bochner integral supply the analytic operations."))), DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula t = F.Id("T"), s = F.Id("s"), x = F.Id("x"), r = F.Id("R");
        Formula dt = App(F.Id("d"), t), et = App(F.Id("e"), t), gt = App(F.Id("G"), t);
        Formula h = F.Id("H"), z = App(F.Id("Z"), t, s);
        return Disp(Seq(Open, Forall, Sp, D(0), Lt, t, Comma, Sp,
            dt, et, Eq, F.Id("I"), Underscore, Grp(F.Id("U")), Sp, Land, Sp, et, dt, Eq, F.Id("I"), Underscore, Grp(F.Id("U")), Sp, Land, Sp,
            et, gt, et, Eq, Int, Underscore, Grp(D(0)), Caret, Grp(D(1)), Sp,
            z, Caret, Grp(Star), z, Sp, F.Id("d"), s, Close,
            RowBreak, Grp(), Land, Sp, Open, Forall, Sp, x, InMacro, Sp, F.Id("U"), Comma,
            x, Neq, Sp, D(0), Rightarrow, Sp, D(0), Lt, Langle, Sp, x, Comma, App(h,x), Rangle, Close,
            RowBreak, Grp(), Land, Sp, Open, Exists, Sp, r, Ge, Sp, D(0), Comma, Sp,
            Forall, Sp, t, Comma, Sp, Open, D(0), Lt, t, Le, Sp, D(1), Sp, Land, Sp,
            t, new Formula.Norm(F.Id("b")), Lt, D(1), Close, Sp, Rightarrow, Sp,
            new Formula.Norm(Seq(et,gt,et,Minus,h)), Le, Sp, r,t, Close));
    }

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
