using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;
internal sealed class SilverSlopeAbelianSingularPackingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular-window separation and packing", H("Singular-window separation and packing"), Blocks(
            Describe.Lean(DescribeId.Create("silver-singular-separation"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianSingularPacking.silver_singular_separation"),
                H("Singular starts are separated"),StatementSource.FromAuthor(Disp(Separation())),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "Two exceptional q-window counts place their phases in an interval of length alpha to the power k+1. A closer return contradicts the best approximation bound. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("silver-no-q-length"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianSingularPacking.silver_no_q_length"),
                H("Failure of period q forces a long word"),StatementSource.FromAuthor(Disp(Packing())),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "Every residue modulo q needs a singular full window. Their separated starts give the length bound by an injection into quotient intervals. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem)),[]));

    private static Formula Separation()
    {
        Formula u=F.Id("u"),v=F.Id("v");
        return For(["k","u","v"],Imp(And(Le(D(1),K),Lt(u,v),Ne(C(Q,u),T),Ne(C(Q,v),T)),Le(Next,Sub(v,u))));
    }
    private static Formula Packing()
    {
        Formula n=F.Id("n"),i=F.Id("i");
        return For(["k","n","i"],Imp(And(Le(D(1),K),Lt(Q,n),Not(AP(n,i,Q))),
            Le(Add(Mul(Sub(Q,D(1)),Next),Q),n)));
    }

    private static Formula K => F.Id("k");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula A => Call("silverSlope");
    private static Formula Q => Call("P", Add(K, D(1)));
    private static Formula T => Call("P", K);
    private static Formula Next => Call("P", Add(K,D(2)));
    private static Formula B(Formula n, Formula i) => Call("lowerMechanicalFactor",A,D(0),n,i);
    private static Formula C(Formula n, Formula i) => Call("count",F.Id("true"),B(n,i));
    private static Formula AP(Formula n, Formula i, Formula m) => Call("AbelianPeriod",B(n,i),m);
    private static Formula Not(Formula f) => Seq(Neg,Parenthesized(f));
    private static Formula Ne(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Lt(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Le(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Imp(Formula x,Formula y) => new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Add(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula And(params Formula[] f)
    {
        Formula r=f[^1];
        for(int j=f.Length-2;j>=0;j--) r=new Formula.Logic(f[j],FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula All(string name,Formula type,Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula For(string[] names,Formula body)
    {
        for(int j=names.Length-1;j>=0;j--) body=All(names[j],N,body);
        return body;
    }
    private static Formula Call(string name,params Formula[] arguments)
    {
        var items=new List<Formula>();
        for(int j=0;j<arguments.Length;j++)
        {
            if(j>0) items.AddRange([Comma,Sp]);
            items.Add(arguments[j]);
        }
        return Seq(Operatorname,Grp(F.Id(name)),Parenthesized(Seq([.. items])));
    }
    private static Formula Parenthesized(Formula f) => Seq(Open,f,Close);}
