using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitSeptitMaximumPurityDocument : IScribeDocumentDefinition
{
    private static Formula D(long n) => Num(n);
    private static Formula X(string n) => F.Id(n);
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(n.Contains('.') ? Seq(X(n.Split('.')[0]), Dot, X(n.Split('.')[1])) : X(n), [..xs]);
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Sp,Par(Seq(X(n), Colon, t)), Comma, Par(f));
    private static Formula Ex(string n, Formula t, Formula f) => Seq(Exists, Sp,Par(Seq(X(n), Colon, t)), Comma, Par(f));
    private static Formula And(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[]{Par(f)} : new[]{Land, Sp,Par(f)}).ToArray());
    private static Formula Eqn(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp,b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Rightarrow, Sp,Par(b));
    private static Formula Mul(Formula a, Formula b) => Seq(a, Cdot, Sp,b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a,Comma,b));
    private static Formula J(Formula m, Formula n) => Par(Seq(Fin(m),Times, Sp,Fin(n)));
    private static Formula Mat(Formula j) => Call("Matrix",j,j,C);
    private static Formula Trace(Formula a) => Call("trace",a);
    private static Formula Purity(Formula a) => Call("re",Trace(Mul(a,a)));
    private static Formula Density(Formula a) => And(Call("PosSemidef",a),Eqn(Trace(a),D(1)));
    private static Formula Max => Frac(D(1),D(25));
    private static Formula Diagonal(Formula j, Formula a, Formula denominator)
    {
        var entries=Seq(X("if"),Par(Eqn(X("i"),a)),X("then"),Frac(D(3),denominator),X("else"),Frac(D(1),denominator));
        return Call("diagonal",Par(Seq(X("fun"),Par(Seq(X("i"),Colon,j)),Mapsto, Sp,entries)));
    }
    private static Formula StateExists(Formula p, bool prescribed=false)
    {
        var rho=X("rho"); var j=J(D(4),D(7));
        var facts=And(Density(rho),Call("APPT",rho),Eqn(Purity(rho),p));
        if(prescribed) facts=And(Eqn(rho,Diagonal(j,Pair(D(0),D(0)),D(30))),facts);
        return Ex("rho",Mat(j),facts);
    }
    private static Formula MaximumStatement()
    {
        var rho=X("rho"); var p=X("p");
        var values=Seq(OpenBrace,p,Colon,R,Mid, Sp,StateExists(p),CloseBrace);
        return And(All("rho",Mat(J(D(4),D(7))),Imp(And(Density(rho),Call("APPT",rho)),Le(Purity(rho),Max))),
            Eqn(Call("sSup",values),Max),StateExists(Max,true));
    }
    private static DocumentBlock Desc(string n, string title, Formula f, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("appt-quadbit-septit-"+n.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSeptitMaximumPurity."+n),
            H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra")),
            Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum purity of a literal four-by-seven APPT density matrix is 1/25.",
        H("Four-by-seven APPT maximum purity"),Blocks(
        Desc("claim","Literal density-matrix extremum",Seq(X("claim"),Iff,Sp,Par(MaximumStatement())),
            "The matrices are complex matrices on Fin 4 times Fin 7. Positive semidefiniteness and complex trace one define the density assumption. APPT quantifies over every global unitary, with partial transpose on the second local factor. The claim combines the universal purity upper bound, the supremum of all attainable real trace-squares, and the explicit diagonal attainer with entry 3/30 at (0,0) and entry 1/30 at every other coordinate. It includes all density matrices, including those with repeated or zero eigenvalues, and makes no assertion about all equality cases.",DescribeRole.Definition),
        Desc("result","Sharp four-by-seven APPT purity",MaximumStatement(),
            "Every literal four-by-seven APPT density has Re trace(rho*rho)<=1/25. The set of all such purities has real supremum 1/25, attained by diagonal (3,1^27)/30. The upper bound uses QuadbitQuintitMaximumPurity.diagonal_spectral_reduction to obtain one antitone, nonnegative, mass-one spectrum l and APPT of its labelled diagonal. Both diagonal_necessary_both and UniformRankFourNecessary.uniform_rank_four_necessary take this exact same labelling e, spectrum l and APPT diagonal. Thus K1 and K2 at [l0,l1,l2,l22,l23,l24,l25,l26,l27] are positive semidefinite, while the sum of l0 through l5 is at most the sum of l18 through l27. The terminal sum minus the initial sum is exactly RankFourLength28Purity.L4 l. Applying RankFourLength28Purity.purity_bound bounds the spectral square sum; the retained trace-square equality returns the bound for the original physical matrix. The necessary mass inequality is used together with both pencils; the pencils alone are not substituted for this stronger hypothesis.",DescribeRole.Theorem),
        Paragraph(Text("For attainment, the existing arbitrary-dimension normalized_ray gives (I+2|v><v|)/(mn+2) for every unit vector v. At m=4,n=7 and v=|00>, normalized_basis_diagonal identifies it with the prescribed diagonal. Its trace-square is (28+8)/(28+2)^2=1/25. Positivity, trace one and APPT come from that same ray theorem: every global unitary sends v to a unit vector, for which the numerator is separable. The attained value proves nonemptiness of the purity set and supplies the lower bound in the supremum equality.")),
        Paragraph(Text("The finite-complement Bell construction, normalized ray and length-28 rational identity are used at their existing interfaces. The new connection is that both necessary spectral tests apply to one actual diagonal of the physical state. Hildebrand's Positive partial transpose from spectra, Phys. Rev. A 76, 052325 (2007), provides the spectral-test setting. This result concerns local dimensions four and seven; it does not establish the full APPT purity conjecture or a result in local dimensions five and five.")))));
}
