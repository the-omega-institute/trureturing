using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostRelativePBWDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostRelativePBW.";
    private static Formula V(string x) => F.Id(x);
    private static Formula C(string name, params Formula[] args)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(Operatorname); tokens.Add(Grp(V(part)));
        }
        var fn = Seq(tokens.ToArray());
        return args.Length == 0 ? fn : new Formula.Apply(fn, [.. args]);
    }
    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Member(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Smul(Formula x, Formula y) => C("smul", x, y);
    private static Formula Ite(Formula x, Formula y, Formula z) => C("ite", x, y, z);
    private static Formula Sign(Formula n) =>
        new Formula.Power(Seq(Open, Minus, D(1), Colon, V("Complex"), Close), n);
    private static Formula Sets => C("Finset", V("Nat"));
    private static Formula PairClause(Formula body) => A("B", Sets, A("C", Sets,
        Imp(C("positiveSet", V("B")), Imp(C("positiveSet", V("C")), body))));
    private static Formula ModeClause(Formula body) => A("r", V("Nat"), A("B", Sets,
        A("C", Sets, Imp(Le(D(1), V("r")), Imp(C("positiveSet", V("B")),
            Imp(C("positiveSet", V("C")), body))))));

    public DocumentDefinition Create()
    {
        var r = V("r"); var b = V("B"); var c = V("C"); var p = V("p");
        var w = C("W", b, c);
        var bp = C("bPrefix", r, b);
        var cp = Add(C("Finset.card", b), C("cPrefix", r, c));
        var bneg = ModeClause(Eqn(C("bneg", r, w), Ite(Member(r, b), D(0),
            Smul(Sign(bp), C("W", C("insert", r, b), c)))));
        var cpos = ModeClause(Eqn(C("c", C("Int.ofNat", r), w), Ite(Member(r, b),
            Smul(Sign(bp), C("W", C("Finset.erase", b, r), c)), D(0))));
        var cneg = ModeClause(Eqn(C("cneg", r, w), Ite(Member(r, c), D(0),
            Smul(Sign(cp), C("W", b, C("insert", r, c))))));
        var bpos = ModeClause(Eqn(C("b", C("Int.ofNat", r), w), Ite(Member(r, c),
            Smul(Sign(cp), C("W", b, C("Finset.erase", c, r))), D(0))));
        var projb = ModeClause(Eqn(C("bneg", r, C("c", C("Int.ofNat", r), w)),
            Ite(Member(r, b), w, D(0))));
        var projc = ModeClause(Eqn(C("cneg", r, C("b", C("Int.ofNat", r), w)),
            Ite(Member(r, c), w, D(0))));
        var inversePair = PairClause(And(Eqn(C("invB", C("occ", b, c)), b),
            Eqn(C("invC", C("occ", b, c)), c)));
        var inverseOcc = A("S", Sets, Imp(C("Not", Member(D(3), V("S"))),
            Eqn(C("occ", C("invB", V("S")), C("invC", V("S"))), V("S"))));
        var kill = A("r", V("Nat"), Imp(Le(D(1), r), And(
            Eqn(C("c", C("Int.ofNat", r), V("down")), D(0)),
            Eqn(C("b", C("Int.ofNat", r), V("down")), D(0)))));
        var statement = And(PairClause(Eqn(w, C("Wcoord", b, c))),
            And(A("p", V("pairCarrier"), Eqn(C("basisEquiv", C("Finsupp.single", p, D(1))),
                C("Wrel", p))), And(C("Function.Bijective", V("basisEquiv")),
                And(bneg, And(cpos, And(cneg, And(bpos, And(projb,
                    And(projc, And(inversePair, And(inverseOcc, kill)))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The original countable occupation carrier admits relative ghost pair coordinates with exact signed mode actions.",
            H("Relative bc ghost PBW"), Blocks(
                Paragraph(Text("The carrier is CountableOccupationFock.Fock, the ground state is literally c one vacuum, and the relative submodule is literally the kernel of b zero. W uses ascending finite sets B and C and the product b minus r followed by c minus s, with rightmost action first.")),
                Describe.Lean(DescribeId.Create("bc-ghost-relative-pbw-complete"),
                    DeclarationHandle.Create(Prefix + "relative_pbw_complete"), H("Relative ghost basis and modes"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Wcoord is sign B C times ket of occ B C. The occupation consists of site one precisely when B does not contain one, the even sites twice the difference r minus two for r in B at least two, and the odd sites two times s plus three for s in C. Site three is excluded. The inverse uses the missing site one for the b minus one hole, even-site half-indices plus two for B, and odd-site half-indices minus one above site three for C.")),
                        Paragraph(Text("The sign exponent is the cardinality of C, plus the number of B indices at least three, plus the number of pairs with s plus four at most r, plus one when both one and two belong to B. The last contribution is the exceptional b minus one and b minus two crossing. The counts bPrefix and cPrefix use strict inequality.")),
                        Paragraph(Text("The inverse occupation maps, support characterization of the actual kernel, and a diagonal sign involution construct basisEquiv. It is an actual linear equivalence from finitely supported positive pair coordinates onto that kernel, sending every unit coordinate to the original W. The four mode identities include occupied and absent zero cases. The native bilinears are the displayed coordinate projections. Both inverse laws and annihilation of down by every positive mode are included. The proof uses the original ghost CAR for deletion and the original creation and annihilation ket formulas for insertion; it assumes no basis, spanning or intertwining conclusion.")))),
                Paragraph(Text("This is an algebraic relative ghost result. VOA and CFT completion, anomaly and fusion bridges, BRST nilpotence, quartet contraction, no-ghost, the full string construction, and AdS/CFT remain incomplete.")))));
    }
}
