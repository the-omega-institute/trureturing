using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class StructuredRankOneFamilyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/QuadraticForms/StructuredRankOneFamily.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original finite-puncture simplex domain supplies nonemptiness, constant pivot sign and one globally unique negative diagonal coordinate.",
        H("Continuous structured downdates on the original domain"),
        Blocks(
            Entry("openSimplex", "Independent barycentric coordinates", All(V("m"), Nat,
                Equal(Call("openSimplex", V("m")), Call("setOf", Seq(Typed(V("u"), Arrow(Call("Fin",V("m")),Real)),Sp,Mapsto,Sp,
                    And(All(V("i"),Call("Fin",V("m")),Lt(D(0),Call("u",V("i")))),
                        Lt(SumOver(V("i"),Call("Fin",V("m")),Call("u",V("i"))),D(1))))))), DescribeRole.Definition),
            Entry("punctured_simplex_pathConnected", "Finite punctures preserve path connectedness", Domain(
                Implies(Call("Finite",V("A")),Call("IsPathConnected",Complement))), DescribeRole.Theorem),
            Entry("continuous_family", "Constant sign and the globally unique negative index", Family(), DescribeRole.Theorem),
            Entry("mo513954_revision2", "The complete revision-two conjunction", And(MatrixPart(),Family()), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathoverflow-513954-singular-diagonal-downdate-inertia"), ResolutionKind.Proved)),
            Paragraph(Text("openSimplex(m) is the set of m positive real independent barycentric coordinates whose sum is less than one. Its omitted last coordinate is one minus that sum and is strictly positive. Thus openSimplex(n-1) is exactly an open (n-1)-simplex with n barycentric coordinates. X is any topological space with the displayed homeomorphism e to this model; A is any finite subset of X, and Y is the subtype of points outside A.")),
            Paragraph(Text("The chart from real m-space sends t to exp(t_i)/(1+sum exp(t_j)). Its inverse sends u to log(u_i/(1-sum u_j)). Both maps are continuous and inverse on their full domains. The image of A under the transported chart is finite. For n at least three the real vector-space dimension n-1 is greater than one, so Mathlib's countable-complement theorem supplies a nonempty path-connected complement. Homeomorphic transport establishes nonemptiness and path connectedness of Y. Neither is added as an independent family premise.")),
            Paragraph(Text("The diagonal entries d and vector x are continuous on exactly Y. Delta(y)=pivot(diagonal(d(y)),x(y)) is continuous, nonzero at every point, and therefore has one constant strict sign on connected Y. M is exactly the structured downdate, not an independently supplied family. Its continuity follows from these data and nonvanishing Delta. The positive-semidefinite premise applies at every point of Y.")),
            Paragraph(Text("In the negative-sign case, the additive inertia identity gives negIndex(D)=negIndex(M)+1. Positive semidefiniteness gives negIndex(M)=0 using the existing positive-index/rank identity and the positive-plus-negative rank partition. The real diagonal sign-count theorem therefore supplies exactly one negative diagonal coordinate at every point. For each coordinate j, the set where d_j is negative is open. Its complement is the union of the other negative-coordinate sets, so it is also closed. Nonemptiness selects one j, and connectedness forces its negative set to be all Y. Every other coordinate is nonnegative everywhere, and a point of Y proves global uniqueness.")),
            Paragraph(Text("Together with StructuredRankOneInertia.inertia_downdate specialized to Matrix.diagonal d, these statements establish both source clauses of Lucid's MO513954 revision 2. Singular matrices, every finite matrix dimension, both signs and all zero multiplicities are retained. There is no extra invertibility, spectral gap, tolerance, compactness or supplied connectedness assumption. The open-simplex definition, explicit domain chart and finite-puncture transport, global fixed-index argument, and complete conjunction here are repository-derived. Lucid's revision supplies the source questions and proposed matrix mechanism, not an attestation of these completed theorems. The matrix argument implements the author's proposed block-congruence mechanism and standard Sylvester inertia; no ordinary novelty or global openness claim is made. Public theorem audit registration remains unfinished under issue #25408.")))));

    private static DocumentBlock Entry(string name, string title, Formula formula, DescribeRole role,
        OpenProblemResolutionClaim? resolutionClaim = null) => Describe.Lean(
        DescribeId.Create("structured-rank-one-family-"+name.Replace('_','-').ToLowerInvariant()), DeclarationHandle.Create(Owner+name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuadraticForms/lucid2026structureddowndate")),
        Blocks(Paragraph(Text(name switch {
            "openSimplex" => "The omitted barycentric coordinate is positive because the displayed sum is strictly less than one.",
            "punctured_simplex_pathConnected" => "The explicit log-ratio chart transports the finite punctures to real space of dimension greater than one.",
            "continuous_family" => "Nonemptiness, the strict sign dichotomy and uniqueness of one global coordinate are all included.",
            _ => "Both universal source clauses hold together, with the matrix clause quantified over every finite dimension."
        }))), role, openProblemResolutionClaim: resolutionClaim);
    private static Formula V(string s) => F.Id(s);
    private static Formula Real => Seq(Mathbb,Grp(V("R")));
    private static Formula Nat => Seq(Mathbb,Grp(V("N")));
    private static Formula Arrow(Formula a, Formula b) => Seq(Open,a,Sp,To,Sp,b,Close);
    private static Formula Typed(Formula a, Formula b) => Seq(Open,a,Sp,Colon,Sp,b,Close);
    private static Formula All(Formula a, Formula t, Formula b) => Seq(Open,Forall,Sp,Typed(a,t),Comma,Sp,b,Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Lt(Formula a, Formula b) => Seq(a,Sp,F.Lt,Sp,b);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula Implies(Formula a, Formula b) => Seq(Open,a,Close,Sp,Rightarrow,Sp,Open,b,Close);
    private static Formula SumOver(Formula i, Formula t, Formula body) => Seq(Sum,Underscore,Grp(Typed(i,t)),Sp,body);
    private static Formula Complement => Call("compl",V("A"));
    private static Formula Y => Call("Subtype",Complement);
    private static Formula Index => Call("Fin",V("n"));
    private static Formula Vec => Arrow(Index,Real);
    private static Formula DY(Formula y) => Call("diagonal",Call("d",y));
    private static Formula Delta(Formula y) => Call("pivot",DY(y),Call("x",y));
    private static Formula M(Formula y) => Call("downdate",DY(y),Call("x",y));
    private static Formula Domain(Formula b) => All(V("n"),Nat,Implies(Seq(D(3),Sp,Le,Sp,V("n")),
        All(V("X"),Call("Type"),Seq(OpenBracket,Call("TopologicalSpace",V("X")),CloseBracket,Sp,
            Implies(Call("Nonempty",Call("Homeomorph",V("X"),Call("openSimplex",Seq(V("n"),Sp,Minus,Sp,D(1))))),
                All(V("A"),Call("Set",V("X")),b))))));
    private static Formula MatrixPart()
    {
        var d=V("d"); var x=V("x"); var k=V("k");
        var a=Call("diagonal",d); var delta=Call("pivot",a,x); var m=Call("downdate",a,x);
        var h=Call("isHermitianDiagonal",d);
        Formula P(Formula z) => Call("posIndex",z);
        Formula N(Formula z) => Call("negIndex",z);
        Formula Z(Formula z) => Call("zeroIndex",z);
        Formula PlusOne(Formula z) => Seq(z,Sp,Plus,Sp,D(1));
        var positive=Implies(Lt(D(0),delta),And(Equal(P(h),PlusOne(P(k))),
            And(Equal(N(k),N(h)),Equal(Z(k),PlusOne(Z(h))))));
        var negative=Implies(Lt(delta,D(0)),And(Equal(P(k),P(h)),
            And(Equal(N(h),PlusOne(N(k))),Equal(Z(k),PlusOne(Z(h))))));
        var body=Implies(Seq(delta,Sp,Neq,Sp,D(0)),Seq(Exists,Sp,Typed(k,Call("IsHermitian",m)),Comma,Sp,
            And(positive,negative)));
        return All(V("n"),Nat,All(d,Vec,All(x,Vec,body)));
    }
    private static Formula Family()
    {
        var y=V("y"); var j=V("j"); var i=V("i");
        var positive=All(y,Y,Lt(D(0),Delta(y)));
        var negative=All(y,Y,Lt(Delta(y),D(0)));
        var fixedIndex=Call("ExistsUnique",Seq(Typed(j,Index),Sp,Mapsto,Sp,
            And(All(y,Y,Lt(Call("d",y,j),D(0))),
                All(i,Index,Implies(Seq(i,Sp,Neq,Sp,j),All(y,Y,Seq(D(0),Sp,Le,Sp,Call("d",y,i))))))));
        var conclusion=And(Call("SetNonempty",Complement),Seq(Open,positive,Sp,Lor,Sp,And(negative,fixedIndex),Close));
        var hypotheses=And(Call("Continuous",V("d")),And(Call("Continuous",V("x")),
            And(All(y,Y,Seq(Delta(y),Sp,Neq,Sp,D(0))),All(y,Y,Call("PosSemidef",M(y))))));
        return Domain(Implies(Call("Finite",V("A")),All(V("d"),Arrow(Y,Vec),All(V("x"),Arrow(Y,Vec),
            Implies(hypotheses,conclusion)))));
    }
}
