using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class BcGhostSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostSquare.";
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
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Cast(Formula x) => C("Int.cast", x);
    private static Formula Cube(Formula x) => Seq(x, Caret, Grp(D(3)));
    private static Formula Int => V("Int");
    private static Formula G(Formula r) => C("c", r);
    private static Formula Q => C("Qg");
    private static Formula Lam(Formula x, Formula body) => Seq(Open,x,Mapsto,body,Close);
    private static Formula Sum(Formula x, Formula type, Formula body) => Seq(FormulaDslSum,Underscore,Grp(x,InMacro,Sp,type),Caret,Grp(V("fin")),body);
    private static Formula FormulaDslSum => F.Sum;
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-square-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create()
    {
        var n=V("n"); var v=V("v");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Full ghost BRST square anomaly",H("The all-integer ghost BRST square"),Blocks(
            Paragraph(Text("The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.")),
            Node("squareTerm",A("n",Int,E(C("squareTerm",n),Smul(Mul(C("div",Neg(D(2,6)),D(2,4)),Sub(Cube(Cast(n)),Cast(n))),Mul(G(Neg(n)),G(n))))),"The coefficient is minus twenty-six over twenty-four; summation includes both signed indices.",DescribeRole.Definition),
            Node("squareTerm_finite",A("v",V("Fock"),C("Function.HasFiniteSupport",Lam(n,C("squareTerm",n,v)))),"The pure-c support theorem at total index zero, reindexed by negation, proves statewise local finiteness."),
            Node("squareAnomaly",A("v",V("Fock"),E(C("squareAnomaly",v),Sum(n,Int,C("squareTerm",n,v)))),"This is the full statewise finite anomaly endomorphism.",DescribeRole.Definition),
            Node("square_anomaly",E(Mul(Q,Q),C("squareAnomaly")),"For an odd charge, the commutator of its square with b is the commutator of Q with its b anticommutator, without an extra factor one half. Mixed anomaly and finite triple-c cancellation identify both b and c commutators with those of the full pure-c anomaly. The difference is scalar by the original Fock commutant theorem. Both operators kill the ghost vacuum, so that scalar is zero. This argument is confined to the ghost sector."),
            Paragraph(Text("This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.")))));
    }
}
