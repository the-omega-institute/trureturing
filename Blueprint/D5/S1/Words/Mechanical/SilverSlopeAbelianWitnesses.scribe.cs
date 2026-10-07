using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;
internal sealed class SilverSlopeAbelianWitnessesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact minimum periods of both silver witness families", H("Exact minimum periods of both silver witness families"), Blocks(
            Describe.Lean(DescribeId.Create("silver-w2-min-period"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianWitnesses.silver_w2_min_period"),
                H("Minimum twice a Pell denominator"),StatementSource.FromAuthor(Disp(For(["k"],Imp(Le(D(1),K),And(Lt(D(0),W2Length),Eq(Min(W2Length,W2Start),Mul(D(2),Q))))))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "The explicit decomposition supplies period 2q. Every smaller period is ruled out, including q and q+t. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("silver-wr-min-period"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianWitnesses.silver_wr_min_period"),
                H("Minimum the adjacent-denominator sum"),StatementSource.FromAuthor(Disp(For(["k"],Imp(Le(D(1),K),And(Lt(D(0),WrLength),Eq(Min(WrLength,WrStart),Add(Q,T))))))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "The parity-dependent decomposition supplies period q+t. Every smaller period is ruled out. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem)),[]));

    private static Formula K => F.Id("k");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula A => Call("silverSlope");
    private static Formula Q => Call("P", Add(K, D(1)));
    private static Formula T => Call("P", K);
    private static Formula B(Formula n, Formula i) => Call("lowerMechanicalFactor",A,D(0),n,i);
    private static Formula Eq(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
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
    private static Formula W2Length => Sub(Add(Mul(Mul(D(2),Q),Add(Q,T)),Q),D(1));
    private static Formula W2Start => Add(Mul(D(2),Q),T);
    private static Formula OddIndex => Eq(Call("natMod",K,D(2)),D(1));
    private static Formula WrLength => Sub(Mul(Add(Mul(D(2),Q),D(1)),Add(Q,T)),Call("if",OddIndex,D(1),D(2)));
    private static Formula WrStart => Call("if",OddIndex,D(0),Add(Q,D(1)));
    private static Formula Min(Formula n,Formula i) => Call("minAbelianPeriod",B(n,i));
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
