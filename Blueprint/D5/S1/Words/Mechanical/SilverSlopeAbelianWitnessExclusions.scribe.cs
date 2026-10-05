using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;
internal sealed class SilverSlopeAbelianWitnessExclusionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All smaller witness periods are excluded", H("All smaller witness periods are excluded"), Blocks(
            Describe.Lean(DescribeId.Create("silver-no-q-period"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_no_q_period"),
                H("The convergent period is absent"),StatementSource.FromAuthor(Disp(NoQ())),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "The endpoint phase displacement and the best approximation bound exclude every possible head alignment. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("silver-w2-no-r-period"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_w2_no_r_period"),
                H("The adjacent-denominator sum is absent from the twice-denominator witness"),StatementSource.FromAuthor(Disp(For(["k"],Imp(Le(D(1),K),Not(AP(W2Length,W2Start,Add(Q,T))))))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "The endpoint floor telescope excludes the adjacent-denominator sum for every possible head alignment. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("silver-short-period-exclusion"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_short_period_exclusion"),
                H("The remaining shorter periods are absent"),StatementSource.FromAuthor(Disp(Short())),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "Word length forces enough complete blocks that the approximation error contradicts the exponent bound. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder."))),DescribeRole.Theorem)),[]));

    private static Formula NoQ()
    {
        Formula n=F.Id("n"),i=F.Id("i");
        return For(["k","n","i"],Imp(And(Le(D(1),K),Le(W2Length,n),
            Imp(Call("Even",K),Or(Eq(i,W2Start),Eq(i,Add(Q,D(1)))))),Not(AP(n,i,Q))));
    }
    private static Formula Short()
    {
        Formula n=F.Id("n"),i=F.Id("i"),m=F.Id("m");
        return For(["k","n","i","m"],Imp(And(Le(D(1),K),Le(W2Length,n),Lt(D(0),m),
            Lt(m,Mul(D(2),Q)),Ne(m,Q),Ne(m,Add(Q,T))),Not(AP(n,i,m))));
    }

    private static Formula K => F.Id("k");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula A => Call("silverSlope");
    private static Formula Q => Call("P", Add(K, D(1)));
    private static Formula T => Call("P", K);
    private static Formula B(Formula n, Formula i) => Call("lowerMechanicalFactor",A,D(0),n,i);
    private static Formula AP(Formula n, Formula i, Formula m) => Call("AbelianPeriod",B(n,i),m);
    private static Formula Not(Formula f) => Seq(Neg,Parenthesized(f));
    private static Formula Eq(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Lt(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Le(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Or(Formula x,Formula y) => new Formula.Logic(x,FormulaLogicOperator.Or,y);
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
