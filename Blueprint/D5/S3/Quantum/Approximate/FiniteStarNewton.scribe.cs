using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate;

internal sealed class FiniteStarNewtonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite contractive diagonal corrects a small all-input multiplicative defect to an exact unital complex star-algebra homomorphism.",
        H("Finite-diagonal exact star correction"), Blocks(
            Paragraph(Text("B and A are unital complex C-star algebras; the norm of the source identity is one. They come with their complete norms, associative multiplication and isometric involutions. J is any finite index type. FiniteDiagonal B J has legs a(j), b(j), product sum a(j)b(j)=1, and algebraic tensor centrality sum (x a(j)) tensor b(j)=sum a(j) tensor (b(j)x) for every x in B. Its norm budget is sum norm(a(j)) norm(b(j))<=1. No completion of the tensor product is used.")),
            Paragraph(Text("For a bounded complex-linear map u, defect(u,x,y)=u(xy)-u(x)u(y). DefectBound u r means norm(defect(u,x,y))<=r norm(x) norm(y) for every x,y. PreservesStar u means u(star(x))=star(u(x)) for every x, exactly. These are global conditions, with no restriction to entries, unitaries or self-adjoint inputs.")),
            Describe.Lean(DescribeId.Create("finite-diagonal-exact-star-correction"),
                DeclarationHandle.Create("D5/S3/Quantum/Approximate/FiniteStarNewton.exists_star_hom_close"),
                H("An exact homomorphism with dimension-free distance"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw correction is w'(x)=sum u(a(j)) defect(u,b(j),x). Its star reflection is star(w'(star(x))); their half sum w is complex-linear and exactly star preserving. The Newton step is u+w. Associativity gives the exact cocycle identity, and tensor centrality identifies its linearized defect. If the defect radius is r, the residual is at most norm(u(1)-1) r+2 r^2. The correction norm is at most norm(u) r.")),
                    Paragraph(Text("The C-star identity applied to star(x)x gives norm(f)^2<=norm(f)+d and hence norm(f)<=3/2. In the neighborhood norm(u)<=2 and norm(u(1)-1)<1/2, the unit defect implies norm(u(1)-1)<=2r. The new multiplicative defect is therefore at most 8r^2. This estimate uses the actual associative target multiplication.")),
                    Paragraph(Text("The prescribed orbit starts at f. Its numerical radii satisfy r(0)=d and r(k+1)=8r(k)^2. Simultaneous induction proves exact linearity and star preservation, defect at most r(k), r(k)<=d/4^k, and norm(u(k)-f)<=(8d/3)(1-4^(-k)). The resulting norm and unit neighborhoods close together. Its increments are at most 2d/4^k, so the orbit converges in operator norm.")),
                    Paragraph(Text("Continuous evaluation, multiplication and star pass to the limit. Vanishing defect gives exact multiplication. The limit's value at one is an idempotent within distance one third of one, which forces it to be one. No polar correction or later normalization changes the distance estimate. Only the defect contracts; uniqueness and contraction of the map-valued Newton operator are not conclusions.")),
                    Paragraph(Text("Finite averaging and correction are motivated by arXiv:2405.02434v2. The constants 1/32, 1/4 and 8/3 are the sufficient constants in the displayed construction. This statement is conditional on an actual finite contractive diagonal and makes no literature originality or full-corner realization claim."))),
                DescribeRole.Theorem))));

    private static Formula X(string n) => F.Id(n);
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Instances(Formula body, params Formula[] xs)
    {
        for (int k=xs.Length-1;k>=0;--k) body=F.Seq(F.OpenBracket,xs[k],F.CloseBracket,F.Sp,body);
        return body;
    }
    private static Formula Statement()
    {
        Formula b=X("B"), a=X("A"), j=X("J"), f=X("f"), d=X("d"), x=X("x");
        Formula close=All("x",b,Le(new Formula.Norm(Subtract(At(X("rho"),x),At(f,x))),
            Multiply(new Formula.Fraction(Multiply(Num(8),d),Num(3)),new Formula.Norm(x))));
        Formula result=Ex("rho",Call("ComplexStarAlgHom",b,a),close);
        Formula assumptions=And(Le(Num(0),d),And(Le(d,new Formula.Fraction(Num(1),Num(32))),
            And(Call("PreservesStar",f),And(Call("DefectBound",f,d),
                Le(new Formula.Norm(Subtract(At(f,Num(1)),Num(1))),new Formula.Fraction(Num(1),Num(4)))))));
        Formula statement=new Formula.TypeArrow(Call("FiniteDiagonal",b,j),
            All("f",Call("ComplexCLM",b,a),All("d",Call("Real"),Imp(assumptions,result))));
        statement=Instances(statement,Call("CStarAlgebra",b),Call("CStarAlgebra",a),
            Call("Fintype",j),Call("NormOneClass",b));
        return All("B",Call("Type"),All("A",Call("Type"),All("J",Call("Type"),statement)));
    }
}
