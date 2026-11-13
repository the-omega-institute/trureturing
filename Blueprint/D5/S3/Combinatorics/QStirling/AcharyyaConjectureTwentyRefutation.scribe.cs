using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QStirling;

internal sealed class AcharyyaConjectureTwentyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/acharyya2024typeb");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full universal pointwise identity in Acharyya's Conjecture 20 fails for one standard signed partition with n = 3 and k = 1: the two sides are 1 and 2.",
        H("Acharyya's pointwise Conjecture 20"),
        Blocks(
            Describe.Lean(DescribeId.Create("acharyya20-full-pointwise-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The original universal pointwise identity"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Context(), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("acharyya20-full-pointwise-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The universal identity is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(X("claim")))),
                AssessedProvenance.FromRepo(Source),
                Counterexample(), DescribeRole.Theorem))));

    private static BlockSequence Context() => Blocks(
        Paragraph(Text("Amrita Acharyya, arXiv:2404.14439v1, Conjecture 20: "),
            Text("“We have that "), Math(Pointwise()),
            Text(" for all π ∈ S_B(⟨n⟩,k).” The journal locator is DOI 10.61091/ars162-14, Conjecture 3.16. The quantifiers range over all natural n and k and every list of finite signed blocks; Standard imposes the original domain, not a finite search window.")),
        Paragraph(Text("Write Blocks = List(Finset(ℤ)), ℓ = length(π), and S_i = block(π,i), with S_i = ∅ outside the list. For a finite signed block S, negate(S) = {−s : s ∈ S}. The absolute extrema used by the source and the implementation are:")),
        Paragraph(Math(ExtremaFormula())),
        Paragraph(Text("The empty minimum and maximum are both zero. On Standard inputs every indexed block is nonempty, so these defaults do not affect the claim. All natural extrema in signed comparisons are coerced to integers. Definition 7 gives the following complete predicate; range(t) is {0,…,t−1}, Icc(a,b) is the integer interval including both endpoints, and pairwise disjointness is literal disjointness of the signed sets.")),
        Paragraph(Math(StandardFormula())),
        Paragraph(Text("Thus the list has 2k+1 nonempty disjoint blocks covering {−n,…,n}; S_0 contains zero and is closed under negation; each even block is the negative of the preceding odd block; the positive absolute minimum belongs to the even block; and the even-block minima strictly increase from zero. There is no positivity restriction on a general signed letter in ros.")),
        Paragraph(Text("Definition 13 fixes zero and complements absolute values while preserving signs. Its total implementation on integers is:")),
        Paragraph(Math(ComplementFormula())),
        Paragraph(Text("Here image(c_n,S) means {c_n(s) : s ∈ S}; complement(n,π) maps this image operation over every block in its original order. For every natural n,k and list π, to standardize, orient every nonzero adjacent pair, and then sort all pairs by the absolute minimum of their even component:")),
        Paragraph(Math(OrientFormula())),
        Paragraph(Math(StandardizeFormula())),
        Paragraph(Text("In this display P is the list indexed by r = 0,…,k−1; Q is its merge sort with comparison minAbs(p₂) ≤ minAbs(q₂); flatten replaces each pair by its odd component followed by its even component. The zero block is retained first. Consequently f(n,k,π) = standardize(k,complement(n,π)), the complement followed by full standardization specified in Lemma 19. This implements the general algorithm with no witness-specific branch. General preservation of Standard and the involution assertion in Lemma 19 are not separately proved here.")),
        Paragraph(Text("For any list π, let U(π) be the union of all its blocks and C(π) = U(π) × range(ℓ). Definition 12(1) and (4) are encoded as the cardinalities of these exact pair sets:")),
        Paragraph(Math(StatisticsFormula())),
        Paragraph(Text("The comparison s ≥ minAbs(S_j) in ros and 0 < s ≤ maxAbs(S_j) in rcb is signed and inclusive. An index j identifies the target block S_j, so a counted pair (s,j) is exactly the source pair (s,S_j) on a partition. The existential earlier-block index ranges over all i < j. The natural-number shift k(k−1) uses truncated subtraction, which agrees with the integer expression for every natural k because the k = 0 factor is zero.")),
        Paragraph(Text("The generating-function equality printed after Conjecture 20 remains unsettled by this result. A failure of the pointwise identity does not decide that separate assertion.")));

    private static BlockSequence Counterexample() => Blocks(
        Paragraph(Text("Use the same original-domain witness throughout:")),
        Paragraph(Math(Disp(Eq(X("pi"), Witness())))),
        Paragraph(Text("At n = 3 and k = 1 its three blocks are nonempty, pairwise disjoint and cover −3 through 3. The zero block is {0}; the even block is the negative of the odd block and contains its positive minimum 1; the even minima are 0 < 1. The proof checks the full Standard predicate by decide +kernel.")),
        Paragraph(Math(Disp(Eq(C("f", D(3), D(1), X("pi")), ImageWitness())))),
        Paragraph(Text("Complementation sends the odd block to {−3,2,1} and the even block to {3,−2,−1}; orientation swaps this pair because the complemented odd block contains its positive absolute minimum. Sorting the single pair leaves it in place. The proof checks the entire output list, not just its statistics.")),
        Paragraph(Math(WitnessStatistics())),
        Paragraph(Text("The proof checks both complete pair sets by decide +kernel. Their cardinalities are respectively 2 and 1, while k(k−1) = 0. Instantiating the full universal claim at this one admissible witness would give 1 = 2, a contradiction. Complementation followed by orientation changes the cardinality of the signed, inclusive comparison pairs; it does not transport the two ros pairs to two rcb pairs. The problem dossier states the original question, the source correspondence and the limits of this resolution. The generating-function equality and general preservation or involution of f remain separate assertions.")));

    private static Formula X(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula N => Seq(Mathbb, Grp(X("N")));
    private static Formula Z => new Formula.Integers();
    private static Formula B => C("List", C("Finset", Z));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] clauses)
    {
        Formula f = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--) f = new Formula.Logic(Par(clauses[i]), FormulaLogicOperator.And, Par(f));
        return f;
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula All(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Ex(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), type, body);
    private static Formula Set(params Formula[] values) => new Formula.SetLiteral([.. values]);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula S(Formula i) => new Formula.Subscript(X("S"), i);
    private static Formula R(Formula t) => C("range", t);
    private static Formula Negate(Formula t) => new Formula.Negate(t);
    private static Formula List(params Formula[] values) => Seq(OpenBracket, Seq(values.SelectMany((v,i) => i == 0 ? new[] {v} : new[] {Comma, Sp, v}).ToArray()), CloseBracket);
    private static Formula Builder(Formula variable, Formula domain, Formula predicate) => Seq(OpenBrace, variable, Sp, InMacro, Sp, domain, Sp, Bar, Sp, predicate, CloseBrace);
    private static Formula AbsImage() => Seq(OpenBrace, new Formula.Absolute(X("s")), Colon, In(X("s"), X("S")), CloseBrace);
    private static Formula ExtremaFormula() => Disp(All("S", C("Finset", Z), And(
        Eq(C("minAbs", X("S")), C("ite", Eq(X("S"), Set()), D(0), Seq(Min, AbsImage()))),
        Eq(C("maxAbs", X("S")), Seq(Max, Par(Seq(Set(D(0)), Cup, AbsImage())))))));
    private static Formula StandardFormula()
    {
        var n = X("n"); var k = X("k"); var l = X("ell"); var i = X("i"); var j = X("j"); var r = X("r"); var t = X("t");
        var evenR = Multiply(D(2), r); var evenT = Multiply(D(2), t);
        var body = And(Eq(l, Add(Multiply(D(2), k), D(1))),
            All("i", R(l), new Formula.Not(Eq(S(i), Set()))),
            All("i", R(l), All("j", R(l), Imp(new Formula.Not(Eq(i,j)), C("Disjoint", S(i), S(j))))),
            Eq(C("biUnion", R(l), X("S")), C("Icc", Negate(n), n)),
            In(D(0), S(D(0))), Eq(C("negate", S(D(0))), S(D(0))),
            All("r", R(k), Eq(S(Add(evenR,D(2))), C("negate", S(Add(evenR,D(1)))))),
            All("r", R(k), In(C("minAbs", S(Add(evenR,D(2)))), S(Add(evenR,D(2))))),
            Eq(C("minAbs", S(D(0))), D(0)),
            All("r", R(Add(k,D(1))), All("t", R(Add(k,D(1))), Imp(Lt(r,t), Lt(C("minAbs", S(evenR)), C("minAbs", S(evenT)))))));
        return Disp(All("n", N, All("k", N, All("pi", B, Iff(C("Standard",n,k,X("pi")),body)))));
    }
    private static Formula ComplementFormula()
    {
        var n=X("n"); var z=X("z");
        return Disp(All("n", N, All("z", Z, Eq(C("complementLetter",n,z), C("ite",Eq(z,D(0)),D(0),
            C("ite",Lt(D(0),z),Subtract(Add(n,D(1)),z),Negate(Par(Add(Add(n,D(1)),z)))))))));
    }
    private static Formula OrientFormula() => Disp(All("A", C("Finset",Z), All("B",C("Finset",Z),
        Eq(C("orient",X("A"),X("B")), C("ite",In(C("minAbs",X("A")),X("A")),Pair(X("B"),X("A")),Pair(X("A"),X("B")))))));
    private static Formula StandardizeFormula() => Disp(new Formula.Aligned([
        Eq(X("P"),Seq(OpenBracket,C("orient",S(Add(Multiply(D(2),X("r")),D(1))),S(Add(Multiply(D(2),X("r")),D(2)))),Colon,In(X("r"),R(X("k"))),CloseBracket)),
        Eq(X("Q"),C("mergeSort",X("P"),Seq(Par(Seq(X("p"),Comma,X("q"))),Mapsto,Le(C("minAbs",new Formula.Subscript(X("p"),D(2))),C("minAbs",new Formula.Subscript(X("q"),D(2))))))),
        Eq(C("standardize",X("k"),X("pi")),C("cons",S(D(0)),C("flatten",X("Q")))),
        Eq(C("f",X("n"),X("k"),X("pi")),C("standardize",X("k"),C("complement",X("n"),X("pi"))))]));
    private static Formula StatisticsFormula()
    {
        var s=X("s"); var j=X("j"); var i=X("i"); var pi=X("pi");
        var earlier=Ex("i",R(j),In(s,S(i)));
        var ros=Builder(Pair(s,j),C("C",pi),And(earlier,Le(C("minAbs",S(j)),s)));
        var rcb=Builder(Pair(s,j),C("C",pi),And(earlier,Lt(D(0),s),Le(s,C("maxAbs",S(j)))));
        return Disp(All("pi",B,And(Eq(C("rosPairs",pi),ros),Eq(C("rcbPairs",pi),rcb),
            Eq(C("ros",pi),C("card",C("rosPairs",pi))),Eq(C("rcb",pi),C("card",C("rcbPairs",pi))))));
    }
    private static Formula Pointwise() => Eq(C("rcb",C("f",X("n"),X("k"),X("pi"))),Add(C("ros",X("pi")),Multiply(X("k"),Par(Subtract(X("k"),D(1))))));
    private static Formula ClaimFormula() => Disp(Iff(X("claim"),All("n",N,All("k",N,All("pi",B,Imp(C("Standard",X("n"),X("k"),X("pi")),Pointwise()))))));
    private static Formula Witness() => List(Set(D(0)),Set(Negate(D(1)),D(2),D(3)),Set(D(1),Negate(D(2)),Negate(D(3))));
    private static Formula ImageWitness() => List(Set(D(0)),Set(D(3),Negate(D(2)),Negate(D(1))),Set(Negate(D(3)),D(2),D(1)));
    private static Formula WitnessStatistics() => Disp(And(
        Eq(C("rosPairs",X("pi")),Set(Pair(D(2),D(2)),Pair(D(3),D(2)))),
        Eq(C("rcbPairs",C("f",D(3),D(1),X("pi"))),Set(Pair(D(3),D(2)))),
        Eq(C("ros",X("pi")),D(2)),Eq(C("rcb",C("f",D(3),D(1),X("pi"))),D(1))));
}
