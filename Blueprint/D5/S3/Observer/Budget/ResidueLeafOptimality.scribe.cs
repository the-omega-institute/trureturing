using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ResidueLeafOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least positive-weighted cost of identifying sibling residue leaves is "
            + "attained by scanning in decreasing mass order and inferring the last leaf.",
        H("Weighted Identification of Sibling Residue Leaves"),
        Blocks(
            Paragraph(Text(
                "Fix a prime p and a natural number d. Let X be ZMod of p to the power "
                    + "d plus one. The actual response h(c,a) is the maximum index i from "
                    + "zero through d plus one for which the canonical natural representatives "
                    + "of a and c agree modulo p to the power i. The response q(c,a) is "
                    + "the Boolean equality test. Candidates S share one residue modulo "
                    + "p to the power d, and m assigns a strictly positive rational mass "
                    + "to each candidate. No normalization of these masses is required.")),
            Paragraph(Text(
                "P is PassiveProtocol X with natural-number responses. R(T,a) means "
                    + "runPassiveProtocol h T a. I(T,S) means that equal R transcripts "
                    + "for two members of S imply equal targets. C(T,a) is the list of "
                    + "centers in R(T,a), and L(T,a) is its length. For an enumeration "
                    + "u from Fin k onto S, E(u,a) is the center list of the equality "
                    + "scan of List.ofFn of u, executed at a. Elements of S in these "
                    + "formulas are coerced to X. Set V contains exactly the rational "
                    + "costs of actual identifying protocols, as defined below.")),
            Describe.Lean(
                DescribeId.Create("leaf-sibling-weighted-minimum"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/ResidueLeafOptimality.leaf_sibling_weighted_minimum"),
                H("Schedule attainment and the actual weighted minimum"),
                StatementSource.FromAuthor(MinimumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A full-depth answer detects the queried leaf. All other sibling "
                            + "candidates give the same answer at a fixed center, including "
                            + "a center outside the candidate set. Relabeling continuation "
                            + "branches therefore converts actual and equality protocols "
                            + "in both directions while preserving every queried center "
                            + "and each target's count. Identification is retained.")),
                    Paragraph(Text(
                        "The equality scan attains the capped position count. Conversely, "
                            + "the equality-query normal form supplies a schedule no slower "
                            + "at any target than a given identifying tree. Multiplying "
                            + "by positive masses preserves that lower bound, and the "
                            + "rearrangement inequality minimizes the schedule cost by "
                            + "pairing decreasing masses with increasing coefficients. "
                            + "This proves both membership in V and its lower-bound property.")),
                    Paragraph(Text(
                        "For one candidate the coefficient is zero. For k at least two "
                            + "the coefficients are one through k minus two, followed by "
                            + "k minus one twice. Thus the last pair may exchange places "
                            + "without changing cost; earlier unequal coefficients favor "
                            + "the larger mass. A sorted enumeration begins with a maximum "
                            + "mass candidate. With two leaves every enumeration costs "
                            + "one query at either target. The last survivor is inferred "
                            + "without an extra query."))),
                DescribeRole.Theorem))));

    private static Formula Id(string s) => F.Id(s);
    private static Formula X => Id("X");
    private static Formula S => Id("S");
    private static Formula K => Id("k");
    private static Formula T => Id("T");
    private static Formula A => Id("a");
    private static Formula I => Id("i");
    private static Formula O => Id("o");
    private static Formula U => Id("u");
    private static Formula Power(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Rat => Seq(Mathbb, Grp(Id("Q")));
    private static Formula Fin => Call("Fin", K);
    private static Formula Enumeration(Formula u) => Seq(u, Colon, Sp, Call("Equiv", Fin, S));
    private static Formula Mass(Formula a) => Call("m", a);
    private static Formula Coeff => Call("min", Seq(Call("val", I), Plus, D(1)),
        Seq(K, Minus, D(1)));
    private static Formula SumOver(Formula i, Formula type, Formula summand) =>
        Seq(Sum, Underscore, Grp(i, Colon, type), Sp, summand);
    private static Formula Cost => SumOver(A, S, Seq(Mass(A), Sp, Call("L", T, A)));
    private static Formula Identification => Call("I", T, S);

    private static Formula MinimumFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, Id("p"), Comma, Sp, Id("d"), Colon, Sp, Nat, Comma, Sp,
            Call("Prime", Id("p")), Sp, Rightarrow),
        Seq(X, Sp, Eq, Sp, Call("ZMod", Power(Id("p"), Seq(Id("d"), Plus, D(1)))),
            Comma, Sp, Forall, Sp, S, Colon, Sp, Call("Finset", X), Comma),
        Seq(Open, Forall, Sp, A, Sp, InMacro, Sp, S, Comma, Sp,
            Forall, Sp, Id("b"), Sp, InMacro, Sp, S, Comma, Sp,
            Call("ModEq", Power(Id("p"), Id("d")), Call("val", A), Call("val", Id("b"))),
            Close, Sp, Rightarrow),
        Seq(Forall, Sp, Id("m"), Colon, Sp, X, Sp, To, Sp, Rat, Comma, Sp,
            Open, Forall, Sp, A, Sp, InMacro, Sp, S, Comma, Sp,
            D(0), Sp, Lt, Sp, Mass(A), Close, Sp, Rightarrow),
        Seq(K, Sp, Eq, Sp, Call("card", S), Comma, Sp, Forall, Sp, Enumeration(O), Comma, Sp,
            Call("Antitone", Seq(Open, I, Sp, Mapsto, Sp, Mass(Call("o", I)), Close)),
            Sp, Rightarrow),
        Seq(Id("V"), Sp, Eq, Sp, OpenBrace, Cost, Sp, Mid, Sp,
            T, Colon, Sp, Id("P"), Comma, Sp, Identification, CloseBrace, Comma),
        Seq(Open, Forall, Sp, Enumeration(U), Comma, Sp,
            Exists, Sp, T, Colon, Sp, Id("P"), Comma, Sp, Identification, Sp, Land),
        Seq(Open, Forall, Sp, I, Colon, Sp, Fin, Comma, Sp,
            Call("L", T, Call("u", I)), Sp, Eq, Sp, Coeff, Close, Sp, Land),
        Seq(Open, Forall, Sp, A, Sp, InMacro, Sp, S, Comma, Sp,
            Call("C", T, A), Sp, Eq, Sp, Call("E", U, A), Close, Close, Sp, Land),
        Seq(Call("IsLeast", Id("V"), SumOver(I, Fin,
            Seq(Mass(Call("o", I)), Sp, Coeff))), Dot)
    ]));
}
