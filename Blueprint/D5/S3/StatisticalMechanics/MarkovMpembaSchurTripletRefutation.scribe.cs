using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class MarkovMpembaSchurTripletRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.";
    private const string Base = "D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/avitanfactorgelbwaserklimovsky2026mpembatriplets");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four reversible energy levels exhibit the Mpemba effect although every original and every statically Schur-reduced triplet fails the three-level condition.",
        H("A four-level counterexample to the static Schur-reduced triplet test"), Blocks(
            Paragraph(Text(
                "The rate matrix, detailed balance, condition (3), the simple slowest mode and the two-temperature "
                    + "Mpemba effect are the frozen definitions of MarkovMpembaTripletRefutation. There a(i,j) is "
                    + "the rate from j to i on the states Fin N. This module changes only the rates seen by a triplet: "
                    + "instead of the original rates, a triplet may use the rates of the three-level system obtained "
                    + "by statically eliminating the remaining level.")),
            Describe.Lean(
                DescribeId.Create("mpemba-schur-triplet-schurrates"),
                DeclarationHandle.Create(Prefix + "schurRates"),
                H("Static Schur elimination of one level"),
                StatementSource.FromAuthor(Disp(SchurFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Write M = generator(a). The entries are those of the Schur complement "
                        + "M_TT − M_Ts M_ss⁻¹ M_sT of the one-by-one block at s, the elimination of s from the "
                        + "stationary equations with M_ss = −d_s and d_s the total rate leaving s. For distinct i, j "
                        + "different from s the reduced rate from j to i is a(i,j) + a(i,s)a(s,j)/d_s: the direct rate "
                        + "plus the rate of passing through s. Only these entries enter condition (3) for a triplet "
                        + "avoiding s. The elimination is static: it is the Schur complement at eigenvalue zero, "
                        + "which preserves the equilibrium weights but not the slow eigenvalue equation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mpemba-schur-triplet-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The static Schur-reduced triplet implication"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For four levels with strictly increasing energies, positive bath inverse temperature and "
                        + "positive detailed-balance rates, suppose that every ordered triplet fails condition (3) "
                        + "with the original rates, and that for every level s every ordered triplet of the other "
                        + "three levels fails condition (3) with the reduced rates schurRates(a, s). For four levels "
                        + "the complement of a triplet is the single level s, so these are all static Schur-reduced "
                        + "triplets. The claim concludes that no simple slowest mode of the full rate matrix shows "
                        + "the two-temperature Mpemba effect. Both families of triplet hypotheses are assumed, so this "
                        + "implication is weaker than the one using reduced triplets alone, and a counterexample to "
                        + "it refutes both."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mpemba-schur-triplet-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Failed reduced triplets with a Mpemba effect"),
                StatementSource.FromAuthor(Disp(Not(Q("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The witness is the frozen four-level system of MarkovMpembaTripletRefutation: energies "
                            + "E = (0,1,2,64)·log 16, bath inverse temperature βb = 1, r = 16⁻⁶⁴, "
                            + "μ = 2(125 + 1024r)/(15(273 + 256r)), A = 47/48 − μ − 112r/25, "
                            + "B = 3/2 − 3μ/2 − 128r/25, C = 31/20 − 15μ/8, and the rate array "
                            + "[[0,A,B,C],[A/16,0,1,3/5],[B/256,1/16,0,1/10],[Cr,48r/5,128r/5,0]]. "
                            + "Its frozen lemmas give positivity, detailed balance with weights w = (1,1/16,1/256,r), "
                            + "failure of all four original triplets, the simple slowest mode −1 with left eigenvector "
                            + "ℓ = g − μ1 for g = (0,1,2/3,8/15), and a Mpemba effect at 16^(−β₁) = 1023/1024 and "
                            + "16^(−β₂) = 127/128, where 0 < β₁ < β₂ < βb: the hotter initial state has the smaller "
                            + "slow-mode coefficient, a direct cooling effect.")),
                    Paragraph(Text(
                        "The new facts concern the reduced triplets. Eliminating level s leaves one ordered triplet "
                            + "(i,j,k); the four cases are s = 3, 2, 1, 0 with triplets (0,1,2), (0,1,3), (0,2,3) "
                            + "and (1,2,3). With b = schurRates(a, s), x = w(j)/w(i) and y = w(k)/w(j), exact rational "
                            + "evaluation at r = 16⁻⁶⁴ gives b(i,k)(1 + xy/2) − b(j,k)(1 + y/2) ≤ b(i,j)(1 − x) and "
                            + "b(i,k)x ≤ b(j,k) in each case. The first differences are about −0.481, −0.043, "
                            + "−0.476 and −0.458, and the second about −0.912, −0.548, −0.130 and −0.106. Hence both "
                            + "strict inequalities of (3) fail for every reduced triplet, whichever side of 1 contains "
                            + "κ. All hypotheses of the claim hold while the Mpemba effect occurs, so the claim is false.")),
                    Paragraph(Text(
                        "The static reduction sets the eigenvalue to zero in the elimination of the complement, "
                            + "which preserves equilibrium but changes the eigenvalue equation of the slow mode. "
                            + "The counterexample shows that this change can hide the effect from every three-level test."))),
                DescribeRole.Theorem)
        )));

    private static Formula V(string name) => name switch
    {
        "betaB" => new Formula.Subscript(Beta, F.Id("b")),
        "lam" => LambdaLower,
        "ell" => Ell,
        _ => F.Id(name),
    };
    private static Formula Q(string name)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula IndicesN() => Call("Fin", V("N"));
    private static Formula Indices4() => Call("Fin", D(4));
    private static Formula RatesOver(Formula indices) =>
        new Formula.TypeArrow(indices, new Formula.TypeArrow(indices, Real()));
    private static Formula Generator(Formula rates, string row, string column) =>
        Call(Base + "generator", rates, V(row), V(column));
    private static Formula Triplet(Formula rates, string i, string j, string k) =>
        Call(Base + "TripletCondition", V("E"), V("betaB"), rates, V(i), V(j), V(k));
    private static Formula Frac(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula SchurFormula() => All("N", Nat(), All("a", RatesOver(IndicesN()),
        All("s", IndicesN(), All("i", IndicesN(), All("j", IndicesN(),
            Eq(Call("schurRates", V("a"), V("s"), V("i"), V("j")),
                Sub(Generator(V("a"), "i", "j"),
                    Frac(Mul(Generator(V("a"), "i", "s"), Generator(V("a"), "s", "j")),
                        Generator(V("a"), "s", "s")))))))));

    private static Formula ClaimFormula()
    {
        Formula originalTriplets = All("i", Indices4(), All("j", Indices4(), All("k", Indices4(),
            Imp(Lt(V("i"), V("j")), Imp(Lt(V("j"), V("k")), Not(Triplet(V("a"), "i", "j", "k")))))));
        Formula reducedTriplets = All("s", Indices4(), All("i", Indices4(), All("j", Indices4(), All("k", Indices4(),
            Imp(Lt(V("i"), V("j")), Imp(Lt(V("j"), V("k")), Imp(Ne(V("s"), V("i")), Imp(Ne(V("s"), V("j")),
                Imp(Ne(V("s"), V("k")), Not(Triplet(Call("schurRates", V("a"), V("s")), "i", "j", "k")))))))))));
        Formula vector = new Formula.TypeArrow(Indices4(), Real());
        Formula conclusion = All("lam", Real(), All("ell", vector,
            Imp(Call(Base + "IsSlowMode", Call(Base + "generator", V("a")), V("lam"), V("ell")),
                Not(Call(Base + "MpembaEffect", V("E"), V("betaB"), V("ell"))))));
        Formula[] hypotheses =
        [
            Call("StrictMono", V("E")),
            Lt(D(0), V("betaB")),
            All("i", Indices4(), All("j", Indices4(), Imp(Ne(V("i"), V("j")), Lt(D(0), At(V("a"), V("i"), V("j")))))),
            Call(Base + "DetailedBalance", V("E"), V("betaB"), V("a")),
            originalTriplets,
            reducedTriplets,
        ];
        for (var index = hypotheses.Length - 1; index >= 0; index--)
            conclusion = Imp(hypotheses[index], conclusion);
        return IffOf(Q("claim"), All("E", vector, All("betaB", Real(), All("a", RatesOver(Indices4()), conclusion))));
    }
}
