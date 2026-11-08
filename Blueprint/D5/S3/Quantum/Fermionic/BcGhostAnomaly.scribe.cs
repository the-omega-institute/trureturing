using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class BcGhostAnomalyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostAnomaly.";
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
    private static Formula Cube(Formula x) => Seq(x, Caret, Grp(D(3)));
    private static Formula Int => V("Int");
    private static Formula Zero => D(0);
    private static Formula G(Formula r) => C("c", r);
    private static Formula Q => C("Qg");
    private static Formula R(Formula r) => C("R", r);
    private static Formula L(Formula r) => C("L", r);
    private static Formula Anti(Formula x, Formula y) => Add(Mul(x,y),Mul(y,x));
    private static Formula Comm(Formula x, Formula y) => Sub(Mul(x,y),Mul(y,x));
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-anomaly-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create()
    {
        var r=V("r"); var m=V("m");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Mixed Virasoro anomaly of the cubic ghost charge",H("The actual ghost BRST Virasoro anomaly"),Blocks(
            Paragraph(Text("The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.")),
            Node("R_covariance",A("m",Int,A("r",Int,E(Comm(L(m),R(r)),Smul(Cast(Sub(Mul(Neg(D(2)),m),r)),R(Add(m,r)))))),"The actual c Ward identity acts on each pure-c pair. A bijective integer shift aligns both finite sums and their coefficients combine to minus two m minus r."),
            Node("Qg_odd",E(Anti(C("parity"),Q),Zero),"Actual occupation parity anticommutes with each b and c mode. A product of three odd modes remains odd, and statewise finite supports justify passing parity through the cubic sum."),
            Node("anomalyCoefficient",A("r",Int,E(C("anomalyCoefficient",r),Mul(C("div",D(2,6),D(1,2)),Sub(Cube(Cast(r)),Cast(r))))),"This coefficient uses the ghost central charge minus twenty-six and the commutator direction.",DescribeRole.Definition),
            Node("mixed_anomaly",A("r",Int,E(Comm(Q,L(r)),Smul(Mul(C("div",D(2,6),D(1,2)),Sub(Cube(Cast(r)),Cast(r))),G(r)))),"Graded Jacobi, both cubic Ward identities, finite R covariance and the actual Virasoro theorem make the residual anticommute with all b and c. Multiplication by actual parity puts it in the scalar commutant; oddness forces it to vanish."),
            Paragraph(Text("This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.")))));
    }
}
