using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class UniformRankFourNecessaryDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) => new Formula.Apply(Id(s), [.. a]);
    private static Formula All(string s, Formula t, Formula body) =>
        Seq(Forall, Sp, Open, Id(s), Colon, t, Close, Comma, Sp, body);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula And(Formula a,Formula b) => Seq(Par(a),Land,Sp,Par(b));
    private static DocumentBlock Desc(string name,string title,Formula f,string text,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("uniform-rank-four-"+name.Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary."+name),
            H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),role);

    public DocumentDefinition Create()
    {
        var total = Call("multiply",Id("m"),Id("n"));
        Formula statement = Seq(
            Call("APPT",Call("diagonal",Call("label",Id("lambda"),Id("e")))),Rightarrow,Sp,
            Call("sumFirst",Num(6),Id("lambda")),Leq,Sp,Call("sumLast",Num(10),Id("lambda")));
        statement = All("lambda",Call("RealVector",total),statement);
        statement = All("e",Call("Equiv",Call("Product",Call("Fin",Id("m")),Call("Fin",Id("n"))),Call("Fin",total)),statement);
        statement = Seq(Par(And(Seq(Num(4),Leq,Id("m")),Seq(Num(4),Leq,Id("n")))),Rightarrow,Sp,statement);
        statement = All("n",Id("Nat"),statement);
        statement = All("m",Id("Nat"),statement);
        return DocumentDefinition.Create(ScribeNode.Create(
        "A fixed rank-four product-local APPT test for arbitrary larger local dimensions.",
        H("Uniform rank-four necessity"),Blocks(
            Desc("sumFirst","Initial spectral mass",Call("sumFirst",Id("k"),Id("lambda")),
                "For a real vector lambda indexed by Fin N, sumFirst k lambda is the sum at indices 0 through k-1. An index outside Fin N contributes zero. All uses here have k<=N.",DescribeRole.Definition),
            Desc("sumLast","Terminal spectral mass",Call("sumLast",Id("k"),Id("lambda")),
                "For k<=N, sumLast k lambda is the sum at indices N-k through N-1. Its guarded Fin k expression uses index N-k+i and contributes zero if that index is out of range.",DescribeRole.Definition),
            Desc("uniform_rank_four_necessary","Six initial entries versus ten terminal entries",
                statement,
                "Let m,n>=4 and let e be any explicit equivalence from Fin m times Fin n to Fin(m*n). If the complex diagonal matrix with entry lambda(e(i,j)) is absolutely PPT, then sumFirst 6 lambda <= sumLast 10 lambda. This statement does not require sorting, nonnegativity, total mass one, strict positivity or distinct entries. In particular it applies to the ordered nonnegative spectrum of an APPT density matrix. It is uniform in both local dimensions at fixed rank four; it does not assert a theorem for arbitrary rank r.",DescribeRole.Theorem),
            Paragraph(Text("Inside the actual product-local four-by-four corner, eta=sum_(i=0)^3 e_(i,i) is unnormalized. Gamma(eta eta*) is SWAP: it sends e_(i,j) to e_(j,i). Its six antisymmetric vectors have eigenvalue -1, its six symmetric pair vectors and four diagonal vectors have eigenvalue +1, and the actual finite complement has eigenvalue zero. For pair order 01,02,03,12,13,23, the rotation uses (e_(i,j)+e_(j,i))/sqrt(2) and (e_(i,j)-e_(j,i))/sqrt(2). Assign spectral indices 0 through 5 to the antisymmetric columns, N-10 through N-7 to the diagonals, and N-6 through N-1 to the symmetric columns. A permutation extends this injective assignment across the whole product space; the rotation extends by identity on the actual complement.")),
            Paragraph(Text("APPT applies to the composed global unitary. Compression to the genuine product corner commutes with partial transpose because the embedding is the product of two local Fin.castLE maps. Testing positivity against eta and applying PartialTransposeTrace.partial_transpose_trace_duality gives the terminal mass minus the initial mass, with coefficient one and no normalization factor. No arbitrary global packing is commuted through partial transpose. At N=28 this difference is exactly RankFourLength28Purity.L4.")),
            Paragraph(Text("To combine this inequality with the two rank-three boundary pencils for a physical state, use one sorted diagonalization and apply both necessity arguments to that same APPT diagonal spectrum. A theorem that separately provides an existential spectrum with the pencils does not identify it with the spectrum used here. The common-spectrum implication is the required connection to length-28 purity and to any subsequent dimension-transfer estimate.")),
            Paragraph(Text("Hildebrand's Positive partial transpose from spectra, Phys. Rev. A 76, 052325 (2007), supplies the spectral-test setting; the existing hildebrand2007pptspectra library note is the citation source. This fixed maximally entangled test is a necessary condition and is not an APPT sufficiency theorem or a priority claim.")))));
    }
}
