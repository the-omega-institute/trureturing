using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DerivativeLayerNormalizedObservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized observation on derivative layers", H("Normalized observation on derivative layers"), Blocks(
            Describe.Lean(DescribeId.Create("derivative-layer-normalized-observation"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation"),
                H("Normalized observation on derivative layers"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let V be an arbitrary finite-dimensional real inner-product space, and W an arbitrary complete real inner-product space. Let B:V→V and C:V→W be arbitrary linear maps. Neither observability of the whole V nor a positive dimension is assumed.")),
                    Paragraph(Text("Put n=dim V, N(j)=the intersection of ker(C B^k) for 0≤k<j, U=N(n) orthogonal complement, E(j)=N(j) intersect N(j+1) orthogonal complement for 0≤j<n. Pi(j):V→V is the actual orthogonal projection onto E(j). All n layer indices are retained, even when their layer is zero. Write b and c for the continuous linear maps associated to B and C; i:U→V is the inclusion. All norms are induced Hilbert operator norms.")),
                    Paragraph(Text("For each endomorphism X of V put L(j)(X)=c composed with X composed with Pi(j) composed with i. Define F(T,s)=sum over j<n of T^(-j) L(j)(exp(T s b)), and P(s)=sum over j<n of s^j/j! L(j)(b^j). The exponential is the actual normed-algebra exponential.")),
                    Paragraph(Text("The projections sum to the inclusion on U. There is a nonnegative K, independent of T and s, for which the displayed estimate holds for every T>0 with T times the norm of b less than one and every s between zero and one.")),
                    Paragraph(Text("Orthogonal differences resolve the descending kernel filtration. Every L(j)(b^k) vanishes for k<j. A uniform Taylor-tail bound for the actual exponential, followed by division by T^j and a finite norm sum, gives the linear error.")),
                    Paragraph(Text("The finite derivative filtration supplies orthogonal geometry, while the exponential power series and Bochner integral supply the analytic operations."))), DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula j = F.Id("j"), x = F.Id("x"), t = F.Id("T"), s = F.Id("s"), k = F.Id("K");
        return Disp(Seq(Open, Forall, Sp, x, InMacro, Sp, F.Id("U"), Comma, Sp,
            Sum, Underscore, Grp(j, Lt, F.Id("n")), Sp, App(Pi, j, x), Sp, Eq, Sp, x,
            Close, Sp, Land, Sp, Open, Exists, Sp, k, Sp, Ge, Sp, D(0), Comma, RowBreak, Grp(),
            Forall, Sp, t, Comma, Sp, s, Comma, Sp,
            Open, D(0), Lt, t, Sp, Land, Sp, t, new Formula.Norm(F.Id("b")), Lt, D(1),
            Sp, Land, Sp, D(0), Le, Sp, s, Le, Sp, D(1), Close, Sp, Rightarrow, Sp,
            new Formula.Norm(Seq(App(F.Id("F"), t, s), Minus, App(F.Id("P"), s))),
            Le, Sp, k, t, Close));
    }

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
