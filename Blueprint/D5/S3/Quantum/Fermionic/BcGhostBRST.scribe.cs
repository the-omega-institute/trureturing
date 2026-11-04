using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class BcGhostBRSTDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostBRST.";
    private static Formula V(string x) => F.Id(x);
    private static Formula C(string name, params Formula[] args)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(Operatorname); tokens.Add(Grp(F.Id(part)));
        }
        var fn = Seq(tokens.ToArray());
        return args.Length == 0 ? fn : new Formula.Apply(fn, [.. args]);
    }
    private static Formula A(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Smul(Formula x, Formula y) => C("smul", x, y);
    private static Formula E(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Cast(Formula x) => C("Int.cast", x);
    private static Formula Int => V("Int");
    private static Formula B(Formula r) => C("b", r);
    private static Formula G(Formula r) => C("c", r);
    private static Formula Q => C("Qg");
    private static Formula R(Formula r) => C("R", r);
    private static Formula L(Formula r) => C("L", r);
    private static Formula Anti(Formula x, Formula y) => Add(Mul(x,y),Mul(y,x));
    private static Formula Lam(Formula x, Formula body) => Seq(Open,x,Mapsto,body,Close);
    private static Formula Sum(Formula x, Formula type, Formula body) => Seq(FormulaDslSum,Underscore,Grp(x,InMacro,Sp,type),Caret,Grp(V("fin")),body);
    private static Formula FormulaDslSum => F.Sum;
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-brst-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create()
    {
        var p=V("p"); var r=V("r"); var v=V("v");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Both cubic ghost Ward anticommutators",H("Exact Ward identities of the cubic ghost charge"),Blocks(
            Paragraph(Text("The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.")),
            Node("ward_b",A("r",Int,E(Anti(Q,B(r)),L(r))),"The CAR reduction gives two diagonals in the ordered pair sum. Each is half the actual Virasoro sum. The exchanges use supports on v and b r v, including all zero and edge modes."),
            Node("cc_finite",A("r",Int,A("v",V("Fock"),C("Function.HasFiniteSupport",Lam(p,new Formula.Apply(Mul(G(p),G(Sub(r,p))),[v]))))),"On a fixed occupation, p lies between r minus A and A. The statement holds on arbitrary finite linear combinations."),
            Node("rTerm",A("r",Int,A("p",Int,E(C("rTerm",r,p),Smul(Mul(C("div",D(1),D(2)),Cast(Sub(Mul(D(2),p),r))),Mul(G(p),G(Sub(r,p))))))),"This is the coefficient one half times two p minus r in the constrained pure-c quadratic.",DescribeRole.Definition),
            Node("rTerm_finite",A("r",Int,A("v",V("Fock"),C("Function.HasFiniteSupport",Lam(p,C("rTerm",r,p,v))))),"The weighted pure-c family is locally finite on the actual input state."),
            Node("R",A("r",Int,A("v",V("Fock"),E(C("R",r,v),Sum(p,Int,C("rTerm",r,p,v))))),"This is an actual complex-linear operator on the original Fock space.",DescribeRole.Definition),
            Node("ward_c",A("r",Int,E(Anti(Q,G(r)),R(r))),"The diagonal p plus q equal to r is reindexed only after proving its finite support on the actual state."),
            Paragraph(Text("This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.")))));
    }
}
