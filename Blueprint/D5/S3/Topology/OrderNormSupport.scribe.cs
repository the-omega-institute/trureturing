using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OrderNormSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive normalized order-norm support on the original carrier.",
        H("Positive order-norm support"),
        Blocks(
            Paragraph(Text("For every nonzero vector in the original real normed carrier, the closed salient cone with its specified interior unit supplies a real-linear functional nonnegative on the cone, normalized at the unit, bounded by the orderNorm everywhere, and attaining the orderNorm at that vector. The carrier remains arbitrary and possibly incomplete; no finite-dimensionality, completeness, self-duality or prior state-existence premise is introduced.")),
            Describe.Lean(
                DescribeId.Create("positive-order-norm-support"),
                DeclarationHandle.Create("D5/S3/Topology/OrderNormSupport.positive_norm_support"),
                H("Positive norm support on the entire original carrier"),
                StatementSource.FromAuthor(F.Disp(SupportStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let r=orderNorm(a)>0. The two attained cone points r unit-a and r unit+a cannot both be interior, since a common positive decrease would remain a radius. Hahn-Banach support at a noninterior endpoint gives a continuous positive functional with zero endpoint value and positive unit mass; normalize by that mass.")),
                    Paragraph(Text("The endpoint equation gives absolute value r at a, and the exposed positive-bound supplier gives the global order-norm bound. This mathematical reading is consumed directly by the original unit-row closed-ball and semidefinite proofs; it constructs no physical preparation. The four-slot audit remains unfinished under issue 28178."))),
                DescribeRole.Theorem))));

    private static Formula SupportStatement()
    {
        var e = F.Id("E"); var a = F.Id("a"); var beta = F.Id("beta");
        var A = F.Id("A"); var u = Call("unit", A); var n = Call("orderNorm", A);
        var betaLaws = And(All("x", Call("cone", A), Le(F.D(0), Apply(beta, Id("x"))),
            Eq(Apply(beta, u), F.D(1)),
            All("x", e, Le(Call("abs", Apply(beta, Id("x"))), Apply(n, Id("x")))),
            Eq(Call("abs", Apply(beta, a)), Apply(n, a)));
        var exists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("beta"),
            Call("RealLinearReadings", e), betaLaws);
        return All("E", Id("Types"), Implies(Call("RealNormedVectorSpace", e),
            All("A", Call("ConeUnitData", e), All("a", e,
                Implies(new Formula.Relation(a, FormulaRelationOperator.NotEqual, F.D(0)), exists)))));
    }

    private static Formula Id(string s)=>F.Id(s);
    private static Formula Call(string s,params Formula[] a)=>new Formula.Apply(Id(s),[..a]);
    private static Formula Apply(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula All(string s,Formula type,Formula body)=>new Formula.Bind(
        FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),type,body);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(params Formula[] a)
    {
        var r=a[^1];
        for(var i=a.Length-2;i>=0;i--) r=new Formula.Logic(a[i],FormulaLogicOperator.And,r);
        return r;
    }
}
