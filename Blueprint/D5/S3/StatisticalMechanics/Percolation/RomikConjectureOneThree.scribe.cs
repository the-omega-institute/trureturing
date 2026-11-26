using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class RomikConjectureOneThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/akyazizavadski2026romik");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The published open-range cylinder identity determines the rational functions and yields their common regular boundary evaluation.",
        H("Romik Conjecture 1.3 from the open-range Pfaffian identity"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-rational-cylinder-boundary"),
                DeclarationHandle.Create(Prefix + "source_rationalCylinder_boundary"),
                H("Regularity and common boundary evaluation"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Conjecture 1.3, equation (1.2), asks for every integer k≥2 that R_k(k)=R_(k-1)(k). Theorem 1.2, equation (1.1), gives P_C_N(F_m)=R_m(N) for every fixed integer m≥1 and integer N>m. Corollary 4.2, equation (4.4), identifies the same probability with the size-2m Pfaffian of the inverse Kasteleyn matrix on the prescribed endpoints. Equation (5.25) in the proof of Theorem 1.2 identifies that matrix with n=N-1, using the explicit entries of Lemma 4.3, (4.12) and Proposition 5.1. Thus the theorem's sole premise is their published coincidence for every natural m,N with 1≤m<N. That probability-to-Pfaffian bridge is supplied by the paper as an assumption of this formal theorem.")),
                    Paragraph(Text("Here R is a family indexed by all natural m with values in RatFunc over the rationals. The premise compares canonical RatFunc.eval, using RingHom.id on the rationals and the rational cast of N, with pfaffian(cylinderMatrix(m,N)). For each natural k≥2 the six conclusions are R(k)=rationalCylinder(k), R(k-1)=rationalCylinder(k-1), membership of R(k) in regularAt(k), membership of R(k-1) in regularAt(k), and the two canonical evaluations at the rational cast of k each equal pfaffian(cylinderMatrix(k-1,k)).")),
                    Paragraph(Text("Equality on the infinite integer tail determines a rational function, by deleting the finitely many roots of both reduced denominators and applying the polynomial identity principle to cross-products. Specialization at k gives regularity for the functions of sizes k and k-1. The final unit pair removes the last two endpoints at size k. The two evaluations therefore agree, as conjectured. Equation (2.8) of the cited paper gives the common value 1/A_k, where A_k counts alternating-sign matrices of order k, via the probability of F_(k-1) at circumference 2k. That enumerative identification is a literature consequence outside the formal statement."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        Formula r = F.Id("R"), m = F.Id("m"), N = F.Id("N"), k = F.Id("k");
        Formula prev = Subtract(k, D(1)), rk = Apply(F.Id("R"), k), rp = Apply(F.Id("R"), prev);
        Formula commonValue = Pf(prev, k);
        Formula hypothesis = All("m", Nat, All("N", Nat, Imp(Both(Leq(D(1), m), Lt(m, N)),
            Eq(Eval(N, Apply(F.Id("R"), m)), Pf(m, N)))));
        Formula conclusion = Both(Eq(rk, Call("rationalCylinder", k)),
            Both(Eq(rp, Call("rationalCylinder", prev)),
            Both(Member(rk, Call("regularAt", k)),
            Both(Member(rp, Call("regularAt", k)),
            Both(Eq(Eval(k, rk), commonValue), Eq(Eval(k, rp), commonValue))))));
        return Disp(All("R", new Formula.TypeArrow(Nat, RatFunc),
            Imp(hypothesis, All("k", Nat, Imp(Leq(D(2), k), conclusion)))));
    }

    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula RatFunc => Call("RatFunc", Rat);

    private static Formula Pf(Formula m, Formula x) => Call("pfaffian", Call("cylinderMatrix", m, x));
    private static Formula Eval(Formula x, Formula f) => Call("eval", x, f);

}
