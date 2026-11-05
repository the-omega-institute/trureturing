using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProbabilityTransport;

internal sealed class WeightedProjectionMinorsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Geometry/meler2024weightedminors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted two-minor and three-minor inequality", H("The weighted two-minor and three-minor inequality"),
        Blocks(
            Paragraph(Text("Let n be any natural number, let I=Fin(n), and let x,y,z be orthonormal vectors in the native real Euclidean space on I. For real coordinate vectors define pairMinor(x,y)(i,j)=x(i)y(j)-x(j)y(i). Define tripleMinor(x,y,z)(i,j,k) as the literal three-by-three determinant whose rows are x,y,z and whose columns are i,j,k. The sums below contain each increasing pair or triple once. The nested maximum is the maximum of exactly A(i,j), A(i,k), and A(j,k).")),
            Describe.Lean(DescribeId.Create("weighted-minors"),
                DeclarationHandle.Create("D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.weighted_minors"),
                H("Every positive symmetric real weight matrix satisfies the comparison"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Orthonormal means all three vectors have norm one and every two distinct vectors have inner product zero. The theorem applies to every such triple for every n at least three. The coordinate proof only requires the unit norm of z and its orthogonality to x and y; native Euclidean inner-product and squared-norm formulas discharge these conditions from orthonormality. No positive definiteness, distance condition, nonzero-minor premise, rational-weight restriction, or dimension cutoff is used.")),
                    Paragraph(Text("The finite-array proof sums over all ordered tuples. Skew(v) means v(i,j)=-v(j,i). Alt(b) means b(j,i,k)=-b(i,j,k) and b(k,i,j)=b(i,j,k). The actual maps are lift(z,v)(i,j,k)=z(i)v(j,k)-z(j)v(i,k)+z(k)v(i,j), lower(z,b)(i,j)=sum over k of z(k)b(k,i,j), and contract(z,v)(i)=sum over k of z(k)v(k,i). Pair mass is one half of the full squared-coordinate sum; triple mass is one sixth of its full squared-coordinate sum.")),
                    Paragraph(Text("Finite sum interchange gives the adjoint identity with factor three. Expansion of lower composed with lift and skew symmetry give massThree(lift(z,v))+sum over i of contract(z,v)(i) squared=(sum over k of z(k) squared)massTwo(v). Finite squared Cauchy-Schwarz then bounds massTwo(lower(z,b)) by massThree(b) when z is unit. The zero contracted-mass case is treated separately; no minor is divided by.")),
                    Paragraph(Text("The pinned determinant expansion proves tripleMinor=lift(z,pairMinor), and the two orthogonality equations prove lower(z,tripleMinor)=pairMinor. For every symmetric pair family F, retain its pair coordinates and exactly the triples containing a pair in F. The contraction at a retained pair only sees retained triples. Projection discards nonnegative squares, proving domination for every family, including empty and full families.")),
                    Paragraph(Text("An exact finite threshold expansion represents every nonnegative real value in a finite set as a sum of nonnegative coefficients times indicators of upper level sets. Induction on the maximum constructs the coefficients. Apply the family inequality at every threshold and interchange finite sums. The union condition on the three edges is exactly the upper level condition for the displayed maximum. Equal weights share the same value, so ties and zero minors require no perturbation or approximation.")),
                    Paragraph(Text("Symmetric pair summands occur twice in the full ordered sum. Symmetric triple summands that vanish on repeated indices occur six times. Explicit minimum-index partition and sorting of the other two indices prove these factors; cancellation gives the increasing-index statement. All inequalities are non-strict, including n=3 and equality cases.")),
                    Paragraph(Text("The external question is meler, Inequality involving minors of an orthogonal matrix, MathOverflow 469781, revision F53D06CE-3805-43B9-9FEB-43A79F67F7AB, CC-BY-SA 4.0, also Math StackExchange 4902019. The coordinate proof is a repository synthesis. It directly uses pinned Mathlib squared finite Cauchy-Schwarz and determinant expansions, and assumes no coupling, Hall inequality, exterior norm estimate, or probability normalization."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathoverflow-469781-weighted-orthogonal-minors"),
                    ResolutionKind.Proved))), []));

    private static Formula Statement()
    {
        var symmetry = All("i",Index(),All("j",Index(),Equal(A("i","j"),A("j","i"))));
        var positive = All("i",Index(),All("j",Index(),LT(D(0),A("i","j"))));
        var lhs = SumPairs(Multiply(A("i","j"),Sq(Call("pairMinor",X("x"),X("y"),X("i"),X("j")))));
        var rhs = SumTriples(Multiply(Call("max",A("i","j"),Call("max",A("i","k"),A("j","k"))),
            Sq(Call("tripleMinor",X("x"),X("y"),X("z"),X("i"),X("j"),X("k")))));
        var orthonormal = Call("Orthonormal",Real(),Seq(OpenBracket,X("x"),Comma,X("y"),Comma,X("z"),CloseBracket));
        return All("n",Seq(Mathbb,Grp(X("N"))),All("x",Vec(),All("y",Vec(),All("z",Vec(),
            Imp(orthonormal,All("A",Call("Matrix",Index(),Index(),Real()),
                Imp(And(symmetry,positive),LE(lhs,rhs))))))));
    }

    private static Formula X(string n) => F.Id(n);
    private static Formula Real() => Seq(Mathbb,Grp(X("R")));
    private static Formula Index() => Call("Fin",X("n"));
    private static Formula Vec() => Call("EuclideanSpace",Real(),Index());
    private static Formula A(string i,string j) => Call("A",X(i),X(j));
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula Sq(Formula a) => Seq(Open,a,Close,Caret,Grp(D(2)));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula SumPairs(Formula a) => Seq(F.Sum,Underscore,Grp(X("i"),Comma,X("j"),InMacro,Sp,Index(),Comma,LT(X("i"),X("j"))),Sp,a);
    private static Formula SumTriples(Formula a) => Seq(F.Sum,Underscore,Grp(X("i"),Comma,X("j"),Comma,X("k"),InMacro,Sp,Index(),Comma,LT(X("i"),X("j")),Comma,LT(X("j"),X("k"))),Sp,a);
}
