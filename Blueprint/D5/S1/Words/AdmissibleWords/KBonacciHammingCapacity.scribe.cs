using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciHammingCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Boolean words have sharp Hamming capacity under a fixed forbidden run. "
            + "Their common polynomial remainder image carries a charge giving an actual-length lower bound.",
        H("Hamming capacity and shortest actual words"),
        Blocks(
            Paragraph(Text(
                "Fix a natural order k at least two. A length-n word is a function from Fin n "
                    + "to Bool, read from position zero upwards and accepted by the original "
                    + "scanner forbidding k consecutive true bits. Its Hamming weight wt is "
                    + "the number of true positions. Every false bit occupies a position. "
                    + "Define B_n(i) to be true exactly when i modulo k is below k-1. "
                    + "Define p(0)=0 and p(c)=c+(c-1)/(k-1) for positive c, using natural "
                    + "integer division, and put W_c=B_(p(c)).")),
            Describe.Lean(
                DescribeId.Create("kbonacci-actual-hamming-capacity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciHammingCapacity."
                        + "kbonacci_actual_hamming_capacity"),
                H("Sharp capacity, explicit shortest words, and common charge"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, Sp, F.Id("w"), InMacro, Mathcal, Grp(F.Id("W")),
                    Underscore, Grp(F.Id("n")), Comma, Sp,
                    Operatorname, Grp(F.Id("wt")), Open, F.Id("w"), Close, Sp,
                    Leq, Sp, F.Id("n"), Minus, Lfloor, Sp, F.Id("n"), Slash, F.Id("k"), Rfloor,
                    Qquad, Land, Qquad,
                    Forall, Sp, F.Id("n"), Comma, Sp, F.Id("B"), Underscore, F.Id("n"),
                    InMacro, Mathcal, Grp(F.Id("W")), Underscore, Grp(F.Id("n")), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("wt")), Open, F.Id("B"), Underscore,
                    F.Id("n"), Close, Eq, F.Id("n"), Minus, Lfloor, Sp,
                    F.Id("n"), Slash, F.Id("k"), Rfloor,
                    Qquad, Land, Qquad,
                    Sp, F.Id("p"), Open, D(0), Close, Eq, D(0), Qquad, Land, Qquad,
                    Forall, Sp, F.Id("c"), Comma, Sp,
                    Operatorname, Grp(F.Id("wt")), Open, F.Id("W"), Underscore,
                    F.Id("c"), Close, Eq, F.Id("c"), Sp, Land, Sp,
                    F.Id("W"), Underscore, F.Id("c"), InMacro, Mathcal, Grp(F.Id("W")), Underscore,
                    Grp(F.Id("p"), Open, F.Id("c"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here the script W_n denotes the set of accepted length-n words. "
                            + "For every natural n and every accepted word w, wt(w) is at most "
                            + "n minus the integer quotient n/k. For every n, B_n is accepted "
                            + "and has exactly that weight. For every natural c, W_c is accepted "
                            + "at length p(c), has exactly c true bits, and every accepted "
                            + "length-n word of weight c satisfies p(c) at most n.")),
                    Paragraph(Text(
                        "For each positive c set t=(c-1)/(k-1) and u=c-t(k-1). Then one "
                            + "at most u at most k-1 and p(c)=tk+u. For every j below t and "
                            + "r below k, the bit at actual position jk+r is true exactly "
                            + "when r is below k-1. Every position from tk through p(c)-1 "
                            + "is true. Thus W_c is exactly t ordered copies of k-1 ones "
                            + "followed by a zero, followed by u ones. At c=0 it is the "
                            + "empty word. These statements include k=2, n=0, n below k, "
                            + "multiples of k, and positive multiples of k-1.")),
                    Paragraph(Text(
                        "For every natural d at least two and every nonempty finite set A "
                            + "of natural probe orders a at least two, let Phi_a be X^a minus "
                            + "the sum of X^j for zero at most j below a over ZMod d. Let "
                            + "O(P)(a) be the monic remainder of the same polynomial P by "
                            + "Phi_a, and let H be precisely the range of this remainder "
                            + "array map. Put q equal to the least common multiple over A "
                            + "of gcd(d,a-1). Then q divides d, and there exists a function "
                            + "chi from H to ZMod q such that, for every polynomial P, "
                            + "chi(O(P)) is the natural representative of P evaluated at "
                            + "one, reduced modulo q. The value is independent of the "
                            + "chosen common polynomial source.")),
                    Paragraph(Text(
                        "For every length n and Boolean word w, take the original polynomial "
                            + "P_w to be the sum over actual positions i of X^i with coefficient "
                            + "one when w(i) is true and zero otherwise. The same function chi "
                            + "satisfies chi(O(P_w))=wt(w) modulo q. For every target y in H "
                            + "and every natural c with q at least two and one at most c below "
                            + "q, if chi(y)=c modulo q, then every n and every accepted word "
                            + "w with O(P_w)=y satisfy p(c) at most n. The bound quantifies "
                            + "over all actual realizations, so it also applies when there is "
                            + "no realization. It does not assert that every target of that "
                            + "charge attains this lower bound.")),
                    Paragraph(Text(
                        "Each full disjoint k-position block requires an actual zero; their "
                            + "distinct positions give the capacity count. The periodic word "
                            + "places its zeros exactly at the block ends. Evaluation of each "
                            + "remainder at one modulo gcd(d,a-1) agrees with evaluation of its "
                            + "source polynomial. Congruences for the same pair of source "
                            + "evaluations combine modulo their least common multiple. This "
                            + "uses neither coprimality of the factors nor primality or "
                            + "squarefreeness of d. When q=1 only the trivial charge law remains. "
                            + "The statement concerns the original common remainder range; "
                            + "it makes no separate assertion of a group homomorphism, "
                            + "surjectivity, or full coordinate reconstruction."))),
                DescribeRole.Theorem))));
}
