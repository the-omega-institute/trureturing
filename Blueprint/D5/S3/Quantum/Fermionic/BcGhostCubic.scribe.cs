using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class BcGhostCubicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostCubic.";
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
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Cast(Formula x) => C("Int.cast", x);
    private static Formula Int => V("Int");
    private static Formula Zero => D(0);
    private static Formula B(Formula r) => C("b", r);
    private static Formula G(Formula r) => C("c", r);
    private static Formula Anti(Formula x, Formula y) => Add(Mul(x,y),Mul(y,x));
    private static Formula Lam(Formula x, Formula body) => Seq(Open,x,Mapsto,body,Close);
    private static Formula Sum(Formula x, Formula type, Formula body) => Seq(FormulaDslSum,Underscore,Grp(x,InMacro,Sp,type),Caret,Grp(V("fin")),body);
    private static Formula FormulaDslSum => F.Sum;
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-cubic-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create()
    {
        var p=V("p"); var q=V("q"); var r=V("r"); var v=V("v"); var pq=V("pq");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Statewise locally finite cubic ghost charge",H("The actual normally ordered cubic ghost charge"),Blocks(
            Paragraph(Text("The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.")),
            Node("cubic",A("p",Int,A("q",Int,E(C("cubic",p,q),C("ite",C("LE.le",p,D(1)),C("ite",C("LE.le",q,D(1)),Mul(Mul(G(p),G(q)),B(Sub(Neg(p),q))),C("ite",C("LE.le",Sub(Neg(p),q),Neg(D(2))),Neg(Mul(Mul(G(p),B(Sub(Neg(p),q))),G(q))),Mul(Mul(G(p),G(q)),B(Sub(Neg(p),q))))),C("ite",C("LE.le",q,D(1)),C("ite",C("LE.le",Sub(Neg(p),q),Neg(D(2))),Mul(Mul(G(q),B(Sub(Neg(p),q))),G(p)),Neg(Mul(Mul(G(q),G(p)),B(Sub(Neg(p),q))))),C("ite",C("LE.le",Sub(Neg(p),q),Neg(D(2))),Mul(Mul(B(Sub(Neg(p),q)),G(p)),G(q)),Mul(Mul(G(p),G(q)),B(Sub(Neg(p),q))))))))),"Creators precede annihilators before summation. When b is a creator its cyclic move through both c factors has positive sign. Anticommuting the c factors gives exactly the stable fermionic order; no contraction is added by definition.",DescribeRole.Definition),
            Node("cubicTerm",A("pq",C("Prod",Int,Int),E(C("cubicTerm",pq),Smul(Mul(C("div",D(1),D(2)),Cast(Sub(C("Prod.fst",pq),C("Prod.snd",pq)))),C("cubic",C("Prod.fst",pq),C("Prod.snd",pq))))),"The full ordered pair sum carries the classical factor one half.",DescribeRole.Definition),
            Node("cubic_finite",A("v",V("Fock"),C("Function.HasFiniteSupport",Lam(pq,C("cubic",C("Prod.fst",pq),C("Prod.snd",pq),v)))),"On a basis occupation S, put A equal to its largest site plus three. A live cubic has p and q at most A and p plus q at least minus A. Both indices therefore lie in the finite interval from minus twice A to A. Finite linear combinations give the assertion for every actual state."),
            Node("cubicTerm_finite",A("v",V("Fock"),C("Function.HasFiniteSupport",Lam(pq,C("cubicTerm",pq,v)))),"Weighting cannot enlarge the pointwise support. This fact is consumed by the linear charge and every sum exchange."),
            Node("Qg",A("v",V("Fock"),E(C("Qg",v),Sum(pq,C("Prod",Int,Int),C("cubicTerm",pq,v)))),"This is a genuine complex-linear endomorphism. Its value is defined by a statewise finite sum; the operator family itself is not declared finitely supported.",DescribeRole.Definition),
            Node("cubic_b",A("p",Int,A("q",Int,A("r",Int,E(Anti(C("cubic",p,q),B(r)),Sub(C("ite",E(Add(q,r),Zero),C("normal",Sub(Neg(p),q),p),Zero),C("ite",E(Add(p,r),Zero),C("normal",Sub(Neg(p),q),q),Zero)))))),"Finite CAR reduces the individual cubic to two bilinears with the Virasoro normal ordering."),
            Node("cubic_c",A("p",Int,A("q",Int,A("r",Int,E(Anti(C("cubic",p,q),G(r)),C("ite",E(Add(Sub(Neg(p),q),r),Zero),Mul(G(p),G(q)),Zero))))),"Only the b contraction remains. All signs are checked in the actual operator algebra."),
            Node("Qg_vacuum",E(C("Qg",C("vacuum")),Zero),"An all-creator cubic on the vacuum forces p and q both equal to one, whose repeated c factor is zero. Every other branch has an annihilator on the right. The square proof consumes this vacuum identity."),
            Paragraph(Text("This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.")))));
    }
}
