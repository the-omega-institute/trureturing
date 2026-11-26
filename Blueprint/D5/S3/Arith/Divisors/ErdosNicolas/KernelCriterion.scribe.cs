using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasKernelCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ErdosNicolas/KernelCriterion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict two-block kernel criterion", H("The strict two-block kernel criterion"), Blocks(
            Node("kernel_criterion_blocks", "The block criterion", CriterionFormula(),
                "The finite sets A and B are disjoint; B has at most a times as many points as A. All displayed bounds use those same sets and parameters. The crossResidual is the sum of the short-distance residual w over A×B. KernelTest requires a strictly positive remaining gap R and the strict square comparison R²>4a(bA+1/L)(bB/p+1/L). The proof derives the required energy estimate from kernel positive semidefiniteness rather than assuming it. For a positive prime exponent a, A is D(m) and B is pD(n/p), with pᵃ∥n. At a=0 the prime-power criterion follows directly from the bound on Hhat(m) and nonnegativity of the residual."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false, bool literature = false) => Describe.Lean(
        DescribeId.Create("erdosnicolas-kernelcriterion-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula CriterionFormula()
    {
        var a=V("a"); var l=V("L"); var p=V("p"); var ba=V("bA");
        var bb=V("bB"); var f=V("F"); var A=V("A"); var B=V("B");
        var t=Card(A);
        Formula body=Lt(Call("pairSum", Call("union", A, B)), Mul(Add(a,D(1)),t));
        Formula[] premises=[Lt(D(0),l),Call("Disjoint",A,B),Lt(D(0),t),Le(Card(B),Mul(a,t)),
            Le(Call("pairSum",A),Mul(ba,t)),Le(Call("pairSum",B),Div(Mul(Mul(bb,a),t),p)),
            Le(Call("crossResidual",l,A,B),Mul(f,t)),Call("KernelTest",a,p,l,ba,bb,f)];
        foreach(var premise in premises.Reverse()) body=Imp(premise,body);
        foreach(var name in new[]{"F","bB","bA","p"}) body=All(name,Rat(),body);
        body=All("B",SetNat(),body); body=All("A",SetNat(),body);
        return All("a",Nat(),All("L",Nat(),body));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SetNat() => Call("Finset", Nat());
    private static Formula Card(Formula set) => Call("card", set);
}
