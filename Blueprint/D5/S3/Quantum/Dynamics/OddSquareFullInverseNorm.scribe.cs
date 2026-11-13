using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class OddSquareFullInverseNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An interior repeated odd block forces Euclidean amplification by the whole finite inverse.",
        H("From an interior odd square to the full inverse"),
        Blocks(Describe.Lean(
            DescribeId.Create("full-inverse-unit-amplification"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/OddSquareFullInverseNorm.full_inverse_unit_amplification"),
            H("A unit vector for the complete open block"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let L(t,n) be the sign-conjugated bidiagonal block defined in OddSquareGreenMass, "
                + "and write A(t,n) for the linear map on EuclideanSpace R (Fin n) induced by its inverse. "
                + "All vector norms here are Euclidean. The hoppings are positive and at most one. "
                + "The odd window has length 2q+1, starts at bond 2a, and fits inside the full block: "
                + "a+2q+1 is at most n. Repetition is required only at the 2q stated bond positions. "
                + "There is no exterior or closing bond assumption.")),
                Paragraph(Text(
                "The original forward-substitution inverse formula shows that translating both row "
                + "and column by a transports an entry of the local inverse to the full inverse. "
                + "Thus both exterior portions of the path remain present. All full inverse entries "
                + "are nonnegative. The quadratic paired mass from OddSquareGreenMass therefore "
                + "bounds twice the sum of all entries: each of its two triangular regions embeds "
                + "injectively in the full matrix. The factor two avoids any need to discard overlap. "
                + "For the constant vector x with all coordinates one, this entry sum is the "
                + "Euclidean inner product of x with Ax. Cauchy--Schwarz and the identity "
                + "norm(x) squared equals n give the displayed inequality for v=x/norm(x). "
                + "The hypotheses imply n is positive, so v is defined and has norm one.")),
                Paragraph(Text(
                "This estimate concerns the actual inverse of the full finite bidiagonal block. "
                + "It does not by itself identify an eigenvalue of the full symmetric hopping matrix "
                + "or prove the all-prefix Tribonacci spectral rate. Those conclusions additionally "
                + "require the sublattice spectral identification, the actual word-to-hopping "
                + "substitution, uniform size comparison, and the small prefixes."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t=F.Id("t"); var n=F.Id("n"); var a=F.Id("a"); var q=F.Id("q");
        var i=F.Id("i"); var v=F.Id("v");
        var m=Add(Mul(D(2),q),D(1));
        var positive=All("i",N(),Lt(D(0),At(t,i)));
        var bounded=All("i",N(),Le(At(t,i),D(1)));
        var repeated=All("i",N(),Imp(Lt(i,Mul(D(2),q)),
            Eq(At(t,Add(Mul(D(2),a),Add(i,m))),At(t,Add(Mul(D(2),a),i)))));
        var conclusion=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("v"),
            Call("EuclideanSpace",R(),Call("Fin",n)),
            And(Eq(new Formula.Norm(v),D(1)),
                Le(Mul(q,Add(q,D(1))),Mul(Mul(D(2),n),new Formula.Norm(At(Call("A",t,n),v))))));
        return All("t",new Formula.TypeArrow(N(),R()),All("n",N(),All("a",N(),All("q",N(),
            Imp(positive,Imp(bounded,Imp(Le(D(1),q),Imp(Le(Add(a,m),n),Imp(repeated,conclusion)))))))));
    }

    private static Formula N()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula R()=>Seq(Mathbb,Grp(F.Id("R")));
    private static Formula At(Formula f,params Formula[] xs)=>new Formula.Apply(f,[..xs]);
    private static Formula Call(string name,params Formula[] xs)=>At(Seq(Operatorname,Grp(F.Id(name))),xs);
    private static Formula All(string name,Formula type,Formula body)=>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
}
