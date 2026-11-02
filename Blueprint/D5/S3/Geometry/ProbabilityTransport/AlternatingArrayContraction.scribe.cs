using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProbabilityTransport;

internal sealed class AlternatingArrayContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/ProbabilityTransport/AlternatingArrayContraction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite alternating arrays and minor contraction", H("Finite alternating arrays and minor contraction"),
        Blocks(
            Paragraph(Text("The index type I is arbitrary and finite. All sums use every ordered tuple. Write massTwo(v) for one half of the sum of v(i,j) squared and massThree(b) for one sixth of the sum of b(i,j,k) squared. These denote the Lean definitions mass₂ and mass₃. Skew(v) means v(i,j)=-v(j,i). Alt(b) means b(j,i,k)=-b(i,j,k) and b(k,i,j)=b(i,j,k).")),
            Paragraph(Text("The actual coordinate maps are lift(z,v)(i,j,k)=z(i)v(j,k)-z(j)v(i,k)+z(k)v(i,j), lower(z,b)(i,j)=sum over k of z(k)b(k,i,j), and contract(z,v)(i)=sum over k of z(k)v(k,i). The three-array inner-product identity has factor three; the energy identity below includes the pair multiplicity two and triple multiplicity six.")),
            Node("energy", "Coordinate energy identity", Generic(All("z", Vec(), All("v", Pair(), Imp(Call("Skew", X("v")), Equal(
                Add(Call("massThree", Call("lift", X("z"), X("v"))), Sum("i", Sq(Call("contract", X("z"), X("v"), X("i"))))),
                Multiply(Sum("k", Sq(Call("z", X("k")))), Call("massTwo", X("v")))))))),
                "Finite sum interchange proves adjointness. Expanding lower composed with lift yields the squared norm of z times v, minus the two contraction terms. Skew symmetry combines those terms into minus twice the contraction energy."),
            Node("contraction", "Contraction by a unit vector", Generic(All("z", Vec(), All("b", Triple(), Imp(And(UnitVector(), Call("Alt", X("b"))),
                LE(Call("massTwo", Call("lower", X("z"), X("b"))), Call("massThree", X("b"))))))),
                "Finite squared Cauchy-Schwarz and the energy identity bound the actual contraction. The proof separates zero contracted mass from positive contracted mass; it divides by no minor."),
            Node("recover_minors", "Literal determinant recovery", Generic(Vectors(Imp(Orthogonal(), Equal(
                Call("lower", X("z"), Call("tripleMinor", X("x"), X("y"), X("z"))), Call("pairMinor", X("x"), X("y")))))),
                "pairMinor(x,y)(i,j)=x(i)y(j)-x(j)y(i). tripleMinor(x,y,z)(i,j,k) is the determinant with rows x,y,z and columns i,j,k. The pinned three-by-three determinant expansion gives tripleMinor=lift(z,pairMinor). Unit z orthogonal to x and y then gives the displayed identity. No normalization or mutual orthogonality of x and y is needed."),
            Node("family_domination", "Every pair family is dominated by its neighborhood", Generic(Vectors(All("F", Arrow(X("I"), Arrow(X("I"), X("Prop"))), Seq(
                OpenBracket, Call("DecidableRel", X("F")), CloseBracket, Comma, Sp,
                Imp(And(Orthogonal(), All("i", X("I"), All("j", X("I"), Iff(Call("F", X("i"), X("j")), Call("F", X("j"), X("i")))))),
                    LE(Call("massTwo", Call("pairProjection", X("F"), Call("pairMinor", X("x"), X("y")))),
                        Call("massThree", Call("tripleProjection", X("F"), Call("tripleMinor", X("x"), X("y"), X("z")))))))))),
                "pairProjection retains exactly F. tripleProjection retains exactly the triples with F(i,j) or F(i,k) or F(j,k). Lower at a retained pair uses only retained triples. Projection discards nonnegative square summands, so contraction proves the inequality for every symmetric family, including the empty and full families."),
            Paragraph(Text("These finite-array results supply the coordinate foundation of the weighted-minor comparison posed by meler, Inequality involving minors of an orthogonal matrix, MathOverflow 469781, revision F53D06CE-3805-43B9-9FEB-43A79F67F7AB, CC-BY-SA 4.0, also Math StackExchange 4902019. The coordinate derivation is a repository synthesis. It uses no positive definiteness, metric condition, generic-position premise, coupling, or probability normalization. The conversion to increasing-index sums is a separate identity."))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula X(string n) => F.Id(n);
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Vec() => Arrow(X("I"),Real());
    private static Formula Pair() => Arrow(X("I"),Vec());
    private static Formula Triple() => Arrow(X("I"),Pair());
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n),type,body);
    private static Formula Generic(Formula body) => All("I", X("Type"), Seq(OpenBracket,Call("Fintype",X("I")),CloseBracket,Comma,Sp,body));
    private static Formula Vectors(Formula body) => All("x",Vec(),All("y",Vec(),All("z",Vec(),body)));
    private static Formula Sq(Formula a) => Seq(Open,a,Close,Caret,Grp(D(2)));
    private static Formula Sum(string n, Formula a) => Seq(F.Sum,Underscore,Grp(X(n),InMacro,Sp,X("I")),Sp,a);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula UnitVector() => Equal(Sum("k",Sq(Call("z",X("k")))),D(1));
    private static Formula Orthogonal() => And(UnitVector(),And(Equal(Sum("k",Multiply(Call("z",X("k")),Call("x",X("k")))),D(0)),Equal(Sum("k",Multiply(Call("z",X("k")),Call("y",X("k")))),D(0))));
}
