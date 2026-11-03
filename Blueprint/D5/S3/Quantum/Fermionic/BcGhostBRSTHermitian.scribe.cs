using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostBRSTHermitianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.";
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
    private static Formula E(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Ite(Formula test, Formula yes, Formula no) => C("ite", test, yes, no);
    private static Formula Pair(Formula x, Formula y) => C("Prod.mk", x, y);
    private static Formula Hg(Formula x, Formula y) => C("Hg", x, y);
    private static Formula Int => V("Int");
    private static Formula Fock => V("Fock");
    private static Formula Delta(Formula x, Formula y) => Ite(E(x, y), D(1), D(0));
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-brst-hermitian-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create()
    {
        var p = V("p"); var q = V("q"); var pq = V("pq"); var x = V("x"); var y = V("y");
        var half = C("div", D(1), D(2));
        var band = new Formula.Logic(
            new Formula.Relation(Neg(D(1)), FormulaRelationOperator.LessThanOrEqual, Add(p,q)),
            FormulaLogicOperator.And,
            new Formula.Relation(Add(p,q), FormulaRelationOperator.LessThanOrEqual, D(1)));
        Formula Weighted(Formula a, Formula b, Formula weight) => Ite(E(pq, Pair(a,b)), weight, D(0));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Hermitian symmetry of the original cubic ghost charge", H("The signed occupation form and the cubic ghost charge"), Blocks(
            Paragraph(Text("The carrier is the complex vector space of finitely supported countable occupations. The form Hg is the original signed coefficient pairing, conjugate linear in its first argument and linear in its second; its vacuum functional is minus the coefficient of the occupation {1,3,5}. The b and c modes, their vacuum cuts and the normally ordered cubic are unchanged. The classical bc BRST conventions are described in Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No new physical construction is asserted.")),
            Node("cubicDefect", A("p", Int, A("q", Int, E(C("cubicDefect",p,q), Ite(band, Sub(Delta(p,D(0)), Delta(q,D(0))), D(0))))),
                "Reversing the actual three-factor word and reflecting its modes crosses the normal-order boundary only when minus one is at most p plus q and p plus q is at most one. In that strip the two mixed CAR contractions give delta(p,0) minus delta(q,0).", DescribeRole.Definition),
            Node("Hg_cubic", A("p",Int,A("q",Int,A("x",Fock,A("y",Fock,
                E(Hg(C("cubic",p,q,x),y), Add(Neg(Hg(x,C("cubic",Neg(p),Neg(q),y))), Mul(C("cubicDefect",p,q),Hg(x,C("c",D(0),y))))))))),
                "Apply the all-integer b and c adjoint identities in reverse word order. Away from the middle strip, exchanging the two c factors supplies the minus sign. In the strip, retain both mixed CAR contractions before simplifying their coefficients. This identity includes zero modes and both strip endpoints."),
            Node("cubicTermDefect", A("pq",C("Prod",Int,Int),E(C("cubicTermDefect",pq),
                Add(Add(Add(Weighted(D(0),D(1),Neg(half)),Weighted(D(1),D(0),Neg(half))),Weighted(D(0),Neg(D(1)),half)),Weighted(Neg(D(1)),D(0),half)))),
                "Multiplying by the original real coefficient (p minus q) divided by two leaves exactly four nonzero defects. The pairs (0,1) and (1,0) carry minus one half; (0,minus one) and (minus one,0) carry plus one half.", DescribeRole.Definition),
            Node("Hg_cubicTerm", A("p",Int,A("q",Int,A("x",Fock,A("y",Fock,
                E(Hg(C("cubicTerm",Pair(p,q),x),y),Add(Hg(x,C("cubicTerm",Pair(Neg(p),Neg(q)),y)),Mul(C("cubicTermDefect",Pair(p,q)),Hg(x,C("c",D(0),y))))))))),
                "Conjugating the real coefficient leaves it fixed, while simultaneous mode negation reverses it. Together with the cubic transposition sign this yields the reflected weighted term plus its four boundary defects."),
            Node("Hg_Qg", A("x",Fock,A("y",Fock,E(Hg(C("Qg",x),y),Hg(x,C("Qg",y))))),
                "For the given two states, take the union of their actual finite action supports and the four defect pairs, then adjoin its reflected image. The resulting finite set captures both original statewise sums and is closed under reflection. Finite sesquilinearity and reindexing transpose the sum; the four boundary coefficients add to zero. No finite support of the operator family or common external mode cutoff is assumed."),
            Paragraph(Text("This proves Hermitian symmetry of the original ghost cubic charge on the algebraic signed form. It supplies the ghost adjoint component for a total BRST construction. Total-charge Hermitian integration, nilpotence, cohomology, a no-ghost theorem, Monster moonshine, vertex operator algebra and conformal field theory structures, anomaly and fusion results, string dynamics and AdS/CFT are separate obligations.")))));
    }
}
