using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SandpileCompleteMaximalIdentityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/gaoli2020sandpileidentity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For i,j at least two, the maximal stable configuration lies in the reduced integer Laplacian image at every sink of K_i square P_j exactly for K_4 square P_2.",
        H("Complete maximal identity for clique–path products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sandpile-complete-maximal-identity-at"),
                DeclarationHandle.Create(Module + ".maximalIdentityAt"),
                H("The integer-image condition at a sink"),
                StatementSource.FromAuthor(Disp(MaximalIdentityAtFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For natural i and j, the vertices of the Cartesian product of the complete graph on Fin i "
                    + "and the path on Fin j are pairs. Remove the row and column of the sink s from the integer Laplacian. "
                    + "The condition asks for an integer vector f whose image under this reduced matrix has value "
                    + "degree(v) minus one at each remaining vertex. The degree is a natural number cast to an integer "
                    + "before subtracting one. Gao–Li define the maximal stable configuration and note its recurrence "
                    + "in the arXiv v1 TeX, Paper/Preliminaries.tex, lines 19–29; the reduced matrix and the "
                    + "integer-image criterion for equivalence appear at lines 132–134 and 157–172. "
                    + "Their recurrent identity is the recurrent representative of the zero class, at lines 192–196. "
                    + "Paper/CMIP.tex, lines 8–10 and 37–41, defines the maximal identity property at one sink and at every sink. "
                    + "For i and j at least two, the formula expresses that property through the integer-image criterion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sandpile-complete-maximal-identity-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The clique–path classification"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimProposition()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every pair of natural numbers i and j at least two, every sink of K_i square P_j "
                    + "satisfies the integer-image condition if and only if i equals four and j equals two. "
                    + "This is the reduced-Laplacian reading of Gao–Li's conjecture in the arXiv v1 TeX, "
                    + "Paper/Conjectures.tex, lines 136–140. The source reports computations through fifty "
                    + "at lines 136–142 and proves the cases j equal to two and three beginning at line 144."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sandpile-complete-maximal-identity-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Proof of the classification"),
                StatementSource.FromAuthor(Disp(ClaimProposition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write G for K_i square P_j and L for its integer Laplacian. For a vector f on all vertices, "
                        + "the row at (a,t) is i f(a,t) minus the sum of f(b,t) over b in Fin i, plus the path "
                        + "Laplacian applied to the function u ↦ f(a,u) at t. The path row is the sum of the "
                        + "differences with the predecessor and successor whenever those vertices exist. Its degree "
                        + "counts these two possible neighbours. Summing the path degrees gives 2(j−1); summing "
                        + "degree(v)−1 over the product therefore gives the integer M = i(ij−2).")),
                    Paragraph(Text(
                        "Suppose the image condition holds at s. Extend its integer solution to all vertices by "
                        + "setting f(s)=0. Away from s, Lf equals degree(v)−1. The Laplacian is symmetric and "
                        + "annihilates the constant-one vector, so the sum of the entries of Lf is zero. "
                        + "The total mass M then determines the missing equation at s: at every v, "
                        + "(Lf)(v) = degree(v)−1−M if v=s, and (Lf)(v) = degree(v)−1 otherwise.")),
                    Paragraph(Text(
                        "Take s=(0,0), and compare the clique coordinates a=0 and b=1, which exist because i≥2. "
                        + "Put d(t)=f(a,t)−f(b,t). The clique sums cancel and the two vertices at the same path "
                        + "coordinate have equal degree. Thus i d(t) plus the path Laplacian of d at t is −M "
                        + "at t=0 and zero elsewhere. Reverse the path by setting x(k)=d(j−1−k) for k<j, "
                        + "and x(k)=0 for k≥j. The far endpoint gives x(1)=(i+1)x(0). Each interior row gives "
                        + "x(k+2)=(i+2)x(k+1)−x(k) when k+2<j. The sink endpoint gives "
                        + "(i+1)x(j−1)−x(j−2)=−i(ij−2).")),
                    Paragraph(Text(
                        "Let S denote Polynomial.Chebyshev.S and put u_j=(S ℤ ((j:ℤ)−1)).eval((i:ℤ)+2). "
                        + "The case k=0 uses S ℤ 0=1 and S ℤ (−1)=0. For 1≤k<j, apply "
                        + "bounded_continuant_endpoint to the initial segment ending at k after casting x to a real sequence. "
                        + "Compatibility of Chebyshev evaluation "
                        + "with the integer-to-real map, injectivity of that map, and the Chebyshev recurrence "
                        + "give x(k)=((S ℤ (k:ℤ)).eval(i+2)−(S ℤ ((k:ℤ)−1)).eval(i+2))x(0) for k<j. "
                        + "Substitution at the last two indices, followed by the Chebyshev recurrence, yields "
                        + "(i+1)x(j−1)−x(j−2)=i u_j x(0). Compare this with the sink equation and cancel "
                        + "the nonzero integer i. The integer −x(0) then shows u_j divides ij−2.")),
                    Paragraph(Text(
                        "Cast a_n=(S ℤ n).eval(i+2) to the rationals. The second order recurrence growth theorem "
                        + "with coefficient i+2 makes a_n positive and increasing. Its differences d_n=a_(n+1)−a_n "
                        + "satisfy the same recurrence; applying the theorem again shows they increase from d_0=i+1. "
                        + "Hence d_n>i, and a_(n+2)−in is nondecreasing. At j=3, "
                        + "u_j=i²+4i+3>3i−2; the increment bound extends u_j>ij−2 to every j≥3. "
                        + "Since ij−2 is positive, it cannot be divisible by this larger positive integer. "
                        + "For j=2, the divisibility becomes i+2 dividing 2i−2. Subtracting this from "
                        + "2(i+2) shows i+2 divides six, hence 2≤i≤4. The values two and three fail the "
                        + "original divisibility, leaving precisely i=4.")),
                    Paragraph(Text(
                        "For K_4 square P_2 and an arbitrary sink s, define f(v) to be zero at s, five when "
                        + "v≠s has the same second coordinate as s, six when its second coordinate differs "
                        + "but its first coordinate agrees, and seven otherwise. Restrict f to the non-sink "
                        + "vertices. The product and path row formulas, checked for the finite choices of the "
                        + "two coordinates, give (Lf)(v)=3 at every non-sink vertex; its degree is four. "
                        + "The omitted sink term is zero because f(s)=0, so this restricted vector satisfies "
                        + "the reduced integer Laplacian equations for every s.")),
                    Paragraph(Text(
                        "Finally, the condition at every sink supplies the condition at (0,0), so the "
                        + "divisibility argument forces i=4 and j=2. Conversely, those equalities reduce the "
                        + "required condition at every sink to the explicit vectors just constructed. "
                        + "This establishes exactly the integer-image classification in the displayed proposition; "
                        + "the interpretation through recurrent configurations uses the source's sandpile-group characterization."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gao-li-2020-complete-maximal-identity-clique-path"),
                    ResolutionKind.Proved)))));

    private static Formula MaximalIdentityAtFormula()
    {
        Formula i = X("i"), j = X("j"), s = X("s"), f = X("f"), v = X("v"), w = X("w");
        Formula vertices = VertexType(i, j);
        Formula nonSink = Seq(OpenBrace, v, Colon, Sp, vertices, Sp, Slash, Slash, Sp,
            NotEqual(v, s), CloseBrace);
        Formula graph = At(Qualified("SimpleGraph", "boxProd"),
            Typed(Qualified("Top", "top"), At(Qualified("SimpleGraph"), FinOf(i))),
            At(Qualified("SimpleGraph", "pathGraph"), j));
        Formula Value(Formula x) => At(Qualified("Subtype", "val"), x);
        Formula laplacianEntry = At(Qualified("SimpleGraph", "lapMatrix"), Integers(), graph,
            Value(v), Value(w));
        Formula degree = At(Qualified("SimpleGraph", "degree"), graph, Value(v));
        Formula image = SumOver("w", nonSink, Multiply(laplacianEntry, At(f, w)));
        Formula condition = Some("f", new Formula.TypeArrow(nonSink, Integers()),
            All("v", nonSink, Equal(image, Subtract(CastInteger(degree), Typed(D(1), Integers())))));
        return All("i", Naturals(), All("j", Naturals(), All("s", vertices,
            Equivalence(LocalCall("maximalIdentityAt", i, j, s), condition))));
    }

    private static Formula ClaimProposition()
    {
        Formula i = X("i"), j = X("j"), s = X("s");
        return All("i", Naturals(), All("j", Naturals(),
            Implication(LE(D(2), i), Implication(LE(D(2), j),
                Equivalence(All("s", VertexType(i, j), LocalCall("maximalIdentityAt", i, j, s)),
                    Conjunction(Equal(i, D(4)), Equal(j, D(2))))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(params string[] names) =>
        names.Select(Named).Aggregate((left, right) => Seq(left, Dot, right));
    private static Formula Local(string name) => Named(name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula CastInteger(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Integers());
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula VertexType(Formula i, Formula j) =>
        Seq(FinOf(i), Sp, Times, Sp, FinOf(j));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
}
