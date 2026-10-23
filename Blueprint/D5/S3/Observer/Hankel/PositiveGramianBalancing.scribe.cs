using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class PositiveGramianBalancingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive definite Gramians produce mutually inverse balancing coordinates and an exact Gramian-product spectrum.",
        H("Positive Gramian Balancing"),
        Blocks(
            Describe.Lean(DescribeId.Create("coordinates-type"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.Coordinates"), H("Balancing output"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The output certificate contains the coordinate matrices, positive weights, both inverse identities and both Gramian congruences. Its inhabitation is proved from positive definiteness below."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gramian-root"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot"), H("Positive square root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uses Mathlib's positive continuous-functional-calculus square root."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gramian-root-spec"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot_spec"), H("Root properties"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derives positive definiteness, self-adjointness and the exact square identity for the constructed root."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("diagonal-scalings"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.diagonal_scalings"), H("Inverse diagonal square-root scalings"),
                StatementSource.FromAuthor(Disp(DiagonalScalingsFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive weights w on any finite index type, let D be diagonal(w), H be diagonal(sqrt(w)), and I be diagonal(1/sqrt(w)). Then H I = I H = I D I = 1, and I diagonal(w squared) I = D. These four identities give the inverse coordinate changes and the rescaled Gramian congruences."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinates-nonempty"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates_nonempty"), H("Construction of balancing coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Diagonalizes sqrt(P) Q sqrt(P) using Mathlib's spectral theorem, rescales by fourth roots, and proves both inverse identities and simultaneous congruences. No balancing matrix is an input. This construction is noncomputable and permits repeated eigenvalues."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinates"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates"), H("Chosen constructed coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Selects the output of the proved existence construction. This is an exact mathematical construction, not a floating-point eigensolver."))), DescribeRole.Definition)),
        []));

    private static Formula Parenthesized(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string name,params Formula[] args)
    {
        Formula head=Seq(Operatorname,Grp(name.Split('.').SelectMany((part,index) => index == 0
            ? new Formula[]{F.Id(part)} : new Formula[]{Dot,F.Id(part)}).ToArray()));
        return args.Length == 0 ? head : new Formula.Apply(head,[.. args]);
    }
    private static Formula All(Formula x,Formula type,Formula body) => Seq(Forall,Sp,Parenthesized(Seq(x,Colon,Sp,type)),Comma,Sp,body);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Fun(Formula i,Formula type,Formula body) => Seq(LambdaLower,Sp,Parenthesized(Seq(i,Colon,Sp,type)),Comma,Sp,body);
    private static Formula DiagonalScalingsFormula()
    {
        Formula t=F.Id("iota"),w=F.Id("w"),i=F.Id("i"),d=F.Id("D"),h=F.Id("H"),inv=F.Id("I");
        Formula wi=new Formula.Apply(w,[i]);
        Formula sqrt=Call("Real.sqrt",wi);
        Formula identities=And(Eq(Mul(h,inv),D(1)),And(Eq(Mul(inv,h),D(1)),
            And(Eq(Mul(Mul(inv,d),inv),D(1)),
                Eq(Mul(Mul(inv,Call("diagonal",Fun(i,t,new Formula.Power(wi,D(2))))),inv),d))));
        Formula definitions=Seq(Call("let"),Sp,d,F.Eq,Call("diagonal",w),Comma,Sp,
            Call("let"),Sp,h,F.Eq,Call("diagonal",Fun(i,t,sqrt)),Comma,Sp,
            Call("let"),Sp,inv,F.Eq,Call("diagonal",Fun(i,t,new Formula.Power(Parenthesized(sqrt),new Formula.Negate(D(1))))),Comma,Sp,identities);
        Formula positive=All(i,t,new Formula.Relation(D(0),FormulaRelationOperator.LessThan,wi));
        return All(t,Call("Type"),Seq(OpenBracket,Call("Fintype",t),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",t),CloseBracket,Comma,Sp,
            All(w,new Formula.TypeArrow(t,Seq(Mathbb,Grp(F.Id("R")))),
                new Formula.Logic(Parenthesized(positive),FormulaLogicOperator.Implies,definitions))));
    }
}
