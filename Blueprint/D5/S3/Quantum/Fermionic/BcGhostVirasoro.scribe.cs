using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostVirasoroDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostVirasoro.";
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
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Negate(Formula x) => new Formula.Negate(x);
    private static Formula Int => V("Int");
    private static Formula B(Formula m) => C("b", m);
    private static Formula G(Formula m) => C("c", m);
    private static Formula Zero => D(0);
    private static Formula One => Seq(Open, D(1), Colon, C("Module.End", V("Complex"), V("Fock")), Close);
    private static Formula Ite(Formula condition, Formula yes, Formula no) => C("ite", condition, yes, no);
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-virasoro-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create()
    {
        var m = V("m"); var n = V("n"); var p = V("p"); var q = V("q"); var r = V("r"); var v = V("v");
        Formula L(Formula k) => C("L", k);
        Formula Cast(Formula k) => C("Int.cast", k);
        Formula Comm(Formula x, Formula y) => Sub(Mul(x, y), Mul(y, x));
        var cubic = Sub(Seq(Cast(m), Caret, Grp(D(3))), Cast(m));
        var central = Ite(Eqn(Add(m,n), Zero), Mul(C("div", Negate(D(2,6)), D(1,2)), cubic), Zero);
        return DocumentDefinition.Create(ScribeNode.Create(
            "The normal ordered bc modes on the actual algebraic ghost Fock space satisfy the full integer Virasoro relation with central charge minus twenty-six.",
            H("The actual bc ghost Virasoro representation"), Blocks(
                Paragraph(Text("The carrier is the complex vector space of finitely supported functions on finite subsets of the natural numbers. The b and c operators are exactly the CountableOccupationFock operators with the BcGhostFock vacuum cuts. The construction is the classical algebraic bc system of weights two and minus one; no novelty is claimed. The anomaly is calculated in this representation, using its proved CAR and scalar commutant.")),
                Node("normal", A("p", Int, A("q", Int, Eqn(C("normal",p,q), Ite(Le(p, Negate(D(2))), Mul(B(p),G(q)), Negate(Mul(G(q),B(p))))))), "The b creator is placed on the left. In the other branch the reversed odd product carries a minus sign. This prescription precedes the summation.", DescribeRole.Definition),
                Node("summand", A("m", Int, A("q", Int, Eqn(C("summand",m,q),Smul(Cast(Add(m,q)), C("normal",Sub(m,q),q))))), "The coefficient m plus q implements the ghost conformal weights.", DescribeRole.Definition),
                Node("summand_finite", A("m", Int, A("v", V("Fock"), C("Function.HasFiniteSupport", Seq(Open, q, Mapsto, C("summand",m,q,v), Close)))), "For a basis occupation S, an index outside the interval with radius the absolute value of m plus the largest occupied site plus three forces a rightmost annihilator at an absent site. Finite linear combinations preserve this finite support. The assertion is pointwise in v and does not say that the endomorphism family has finite support."),
                Node("L", A("m", Int, A("v", V("Fock"), Eqn(C("L",m,v), Seq(Sum, Underscore, Grp(q, InMacro, Sp, Int), Caret, Grp(F.Id("fin")), C("summand",m,q,v))))), "Every vector is acted on by the genuine pointwise finite sum. Additivity and complex linearity follow from the proved finite supports.", DescribeRole.Definition),
                Node("ward_b", A("m", Int, A("r", Int, Eqn(Comm(L(m),B(r)), Smul(Cast(Sub(m,r)),B(Add(m,r)))))), "CAR contracts each individual normal product at q equal to minus r. Passing through the sum uses the actual supports on both v and b r v. This is the weight two Ward identity."),
                Node("ward_c", A("m", Int, A("r", Int, Eqn(Comm(L(m),G(r)), Smul(Cast(Sub(Mul(Negate(D(2)),m),r)),G(Add(m,r)))))), "The contraction is at q equal to m plus r. The finite supports on v and c r v justify the exchange. This is the weight minus one Ward identity."),
                Node("centralDefect", A("m",Int,A("n",Int,Eqn(C("centralDefect",m,n),Sub(Comm(L(m),L(n)),Smul(Cast(Sub(m,n)),L(Add(m,n))))))), "The two Ward identities and Jacobi imply that this defect commutes with every actual b and c mode. The existing scalar commutant therefore makes it a scalar operator.", DescribeRole.Definition),
                Node("epsilon", A("v", V("Fock"),Eqn(C("epsilon",v),C("v",C("Finset.empty")))), "This linear functional extracts the empty occupation coefficient.", DescribeRole.Definition),
                Node("virasoro", A("m", Int, A("n", Int, Eqn(Comm(L(m),L(n)),Add(Smul(Cast(Sub(m,n)),L(Add(m,n))),Smul(central,One))))), "The vacuum action is the finite sum over q from n plus two through one. A leftmost b creator has zero empty coefficient, so the pair Ward calculation kills the off-diagonal scalar. On m equal to a nonnegative integer a and n equal to minus a, q equal to one minus r turns the remaining coefficient into the sum of (1-a-r)(2a+1-r) for r from zero through a minus one. Its value is minus thirteen sixths times a cubed minus a. Antisymmetry supplies the negative integers with the opposite sign. The result holds on every finite-excitation vector, without an abstract Virasoro premise or a cutoff."),
                Paragraph(Text("This theorem establishes the algebraic ghost anomaly. It does not establish a BRST charge, its nilpotence or cohomology, a no-ghost theorem, a sewn conformal field theory, complete string dynamics or an AdS/CFT correspondence.")))));
    }
}
