using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;
internal sealed class SilverSlopeAbelianWitnessPeriodsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two silver witness decompositions", H("The two silver witness decompositions"), Blocks(
            Describe.Lean(DescribeId.Create("silver-w2-period"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessPeriods.silver_w2_period"),
                H("Twice a Pell denominator"),StatementSource.FromAuthor(Disp(For(["k"],Imp(Le(D(1),K),AP(W2Length,W2Start,Mul(D(2),Q)))))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "The head has length q, followed by q+t−1 blocks of length 2q and a tail of length 2q−1. Pell phase identities give the required counts. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("silver-wr-period"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessPeriods.silver_wr_period"),
                H("The adjacent-denominator sum"),StatementSource.FromAuthor(Disp(For(["k"],Imp(Le(D(1),K),AP(WrLength,WrStart,Add(Q,T)))))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "At odd index the head is empty. At even index both ends have length q+t−1. The intervening blocks have true count q−t. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem)),[]));

    private static Formula K => F.Id("k");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula A => Call("silverSlope");
    private static Formula Q => Call("P", Add(K, D(1)));
    private static Formula T => Call("P", K);
    private static Formula B(Formula n, Formula i) => Call("lowerMechanicalFactor",A,D(0),n,i);
    private static Formula AP(Formula n, Formula i, Formula m) => Call("AbelianPeriod",B(n,i),m);
    private static Formula Eq(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Le(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Imp(Formula x,Formula y) => new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Add(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
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
