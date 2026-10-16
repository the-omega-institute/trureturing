using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitUniformSpectralBoundDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) => i==0 ? new[] {Parenthesized(f)} : new[] {Land, Sp, Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);


    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula NatValue(Formula x) => Parenthesized(Seq(Parenthesized(Seq(x, Colon, N)), Colon, R));
    private static Formula Prefix(int k) => Sum("i", Fin(Int(k)), Call("l", Id("i")));
    private static Formula Tail(int k) => Sum("i", Fin(Int(k)), Call("l", Add(Sub(Id("N"),Int(k)),Id("i"))));
    private static Formula Bound()
    {
        var n=Id("N"); var l=Id("l"); var fd=Fin(n);
        var t=new Formula.Floor(Frac(Add(Mul(Int(3),n),Int(4)),Int(8)));
        var h=And(Call("Antitone",l),All("i",fd,Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",fd,Call("l",Id("i"))),Int(1)),
            Le(Prefix(3),Tail(6)),Le(Prefix(6),Tail(10)),Le(Call("l",Int(0)),Tail(3)));
        var nr=NatValue(n);var tr=NatValue(t);
        return All("N",N,Imp(Le(Int(67),n),All("l",Arrow(fd,R),Imp(h,
            Le(Sum("i",fd,Pow(Call("l",Id("i")),2)),
                Frac(Add(Mul(Int(9),nr),Mul(Int(16),tr)),Pow(Add(Mul(Int(3),nr),Mul(Int(2),tr)),2)))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three boundary inequalities bound the squared mass of every ordered probability spectrum in every dimension at least 67.",
        H("Three-row scalar spectral bound"),Blocks(
            Paragraph(Text("For l:Fin N to the reals, indices inside prefix and tail sums mean their natural values embedded in Fin N. Thus the three rows compare the first three entries with the last six, the first six with the last ten, and the first entry with the last three. N is arbitrary subject to N at least 67, with zero entries and repeated eigenvalues allowed.")),
            Desc("QuadbitUniformSpectralBound","three_row_scalar_bound","Arbitrary-dimension squared-mass estimate",Bound(),
                "The integer t is natural-number division (3*N+4)/8, equivalently the displayed floor; its real coercion is taken only after that division. N-6, N-10 and N-3 are natural subtractions before indexing. All ratios in the bound are real divisions. The only hypotheses are the displayed ordering, nonnegativity, mass one and three boundary inequalities.",DescribeRole.Theorem),
            Paragraph(Text("The proof first reconstructs the complete spectrum from its adjacent nonnegative gaps, including the final gap to zero. The middle gap mass is compressed to one step length j. Positive middle mass uses barycentric weights; zero middle mass uses a division-free reconstruction. Closure of the Euclidean norm-to-mass cone then transfers estimates for the fixed sixteen-slot boundary cone back to every original spectrum.")),
            Paragraph(Text("For the fixed cone, slack coordinates embed it in the nonnegative kernel of B. The general cofactor hull theorem supplies candidate vectors. A separate full-row padding argument applies to each individual candidate, keeps both signs and a positive scale, and produces an ordered support of size four. Checked witnesses cover all 3876 such supports. Their exact determinant identities, mixed-sign or zero alternatives and positively scaled catalog alternatives yield the 187 original ray identifiers; no assertion of 187 distinct extreme rays is needed.")),
            Paragraph(Text("The catalog rays are reconstructed with the original gap coordinates and slacks. Their exact mass and Gram moments satisfy polynomial certificate inequalities on the whole region N at least 67 and 6 at most j at most N-10. The boundary and middle envelopes are dominated by the rounded integer bulk value. The integer maximization argument retains t=(3*N+4)/8 rather than substituting a continuous maximizer. The resulting cone estimate is constructed in the proof, and trace one together with the square-root identity gives the squared-mass conclusion.")),
            Paragraph(Text("Dependencies are the nonnegative-kernel circuit and cofactor completeness results, the cofactor cross identity in CofactorKernel, the shared spectral norm, step-synthesis, gap and additive-closure lemmas in UniformSpectralBound, and pinned Mathlib linear algebra, convex cone and Euclidean norm results. Circuit decomposition is the fully nonnegative specialization of Mueller and Regensburger's Theorem 3 on elementary vectors of subspace cones, as described in NonnegativeKernelCircuit. Signed cofactor kernels and barycentric mixtures are classical constructions; the particular three-row compression, catalog soundness chain and uniform rounded estimate are derived here. This statement concerns scalar spectra. Connecting these inequalities to a physical APPT model, constructing an attaining state, and identifying a purity supremum require further results.")))));
}
