using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class FiniteBellCornerDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) => i==0 ? new[] {Parenthesized(f)} : new[] {Land, Sp, Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Lt(Formula x, Formula y) => Seq(x, F.Lt, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x, Times, Sp, y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix", i, j, field);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static Formula Trace(Formula m) => Call("Matrix.trace", m);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra")),
            Blocks(Paragraph(Text(prose))), role);



    private static Formula N => Mul(Id("m"),Id("n"));
    private static Formula J => Prod(Fin(Id("m")),Fin(Id("n")));
    private static Formula l => Id("l");
    private static Formula rho => Id("rho");
    private static Formula BoundaryStatement()
    {
        var q=Id("q"); var value=Call("val",q); var total=Id("N");
        var index=Seq(Id("if"),Sp,Lt(value,Int(3)),Sp,Id("then"),Sp,value,
            Sp,Id("else"),Sp,Add(Seq(total,Minus,Int(9)),value));
        return All("N",Id("Nat"),Imp(Le(Int(9),total),
            All("l",Arrow(Fin(total),R),All("q",Fin(Int(9)),
                Eq(Call("boundaryValues",total,l,q),
                    Call("l",Parenthesized(Seq(index,Colon,Fin(total)))))))));
    }
    private static Formula SpectralStatement()
    {
        var boundary=Call("boundaryValues",N,l);
        var purity=Eq(Call("Complex.re",Trace(Mul(rho,rho))),
            Sum("i",Fin(N),Pow(Call("l",Id("i")),2)));
        var conclusion=And(Call("Antitone",l),All("i",Fin(N),Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",Fin(N),Call("l",Id("i"))),Int(1)),
            PSInt(Call("K1",boundary)),PSInt(Call("K2",boundary)),purity);
        var exists=Seq(Exists,Sp,Parenthesized(Seq(l,Colon,Arrow(Fin(N),R))),Comma,Sp,conclusion);
        return All("m",Id("Nat"),All("n",Id("Nat"),Imp(And(Le(Int(3),Id("m")),Le(Int(3),Id("n"))),
            All("rho",Matrix(J,J,C),Imp(And(PSInt(rho),Eq(Trace(rho),Int(1)),Call("APPT",rho)),exists)))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All finite bipartite APPT density matrices with local dimensions at least three satisfy both qutrit Bell-corner constraints on the largest three and smallest six eigenvalues.",
        H("Finite product Bell-corner spectral reduction"),Blocks(
            Desc("FiniteBellCorner","boundaryValues","Nine extremal spectral coordinates",BoundaryStatement(),
                "The total dimension N is at least nine, and the proof argument for that inequality is suppressed in the display. Indices are zero-based. The selector takes entries 0, 1, 2, N−6, N−5, N−4, N−3, N−2, N−1. The middle N−9 entries remain in the full packing, so trace and purity are preserved."),
            Desc("FiniteBellCorner","spectral_reduction","Necessary spectral matrices in arbitrary finite local dimensions",SpectralStatement(),
                "For all natural m,n at least three, every positive semidefinite trace-one complex matrix on Fin m × Fin n satisfying literal APPT has an antitone nonnegative spectrum l of length mn and mass one. The proof argument 9≤mn is suppressed in the displayed boundary selector. Both existing real matrices K1 and K2 evaluated on the nine extremal spectral coordinates are positive semidefinite, and Re trace(rho*rho) equals the sum of all mn spectral squares. Repeated and zero eigenvalues are included. Embed Fin 3 into each local factor. Their product c has a finite complement, identified with Fin(mn−9) by cardinality. Extend the Bell unitary and its swapped partner by identity on this complement. Partial transpose commutes with compression along this product: both entries at (i,j),(k,l) equal rho(c(i,l),c(k,j)). The existing Bell principal identity then gives the two necessary matrices. Ordered spectral diagonalization uses an arbitrary global packing only as a unitary conjugation; it assumes no partial-transpose covariance of that packing. These conditions are necessary and do not assert APPT sufficiency. At mn=24 the boundary equals QutritSpectralReduction.boundaryValues 5 and permits direct use of the existing dimension-24 sharp certificate. Hildebrand Theorem 2, PDF page 5 of quant-ph/0502170, already gives APPT 4×6→3×8 at fixed total dimension 24, so the qutrit maximum and established attaining ray imply the 4×6 scalar value. At total dimension twenty, the selector is SpectralBoundaryTransfer.boundaryValues 11. The length-twenty bound follows by the full rank-three insertion/deletion theorem from endpoint lengths eighteen and twenty-one, first reaching nineteen and then twenty. For the four-by-five product, the normalized coordinate ray (I+2|00><00|)/22 is exactly diagonal (3,1^19)/22. Its trace is one and its trace-square is (20+8)/22^2=7/121. For any global unitary U, the unit vector U|00> yields a separable numerator by LowRankRays.separableCone_one_add_two_rankOne; positive normalization and separableCone_partialTranspose_posSemidef imply APPT. At total dimension twenty-four, the same argument combined directly with QutritN8PurityBound.certificate_bound gives Re trace(rho^2)<=8/169 for every literal four-by-six APPT density. The coordinate ray (I+2|00><00|)/26 has diagonal (3,1^23)/26, is positive semidefinite with trace one, remains PPT after every global unitary, and has purity (24+8)/26^2=8/169. Thus the four-by-six real purity supremum is attained at 8/169. This application uses the existing qutrit bound at fixed total dimension and requires no extra spectral certificate. The varying-total-dimension inference for length twenty is the separate insertion/deletion argument. Neither application describes all maximizers or establishes an unrestricted APPT theorem.",DescribeRole.Theorem))));
}
