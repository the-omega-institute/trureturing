using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Forbidden;

internal sealed class BonaMagaRicheyExtremalFrequencyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/bonamagarichey2026letter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unrestricted proposed maximizers of the limiting avoidance frequency fail at length one.",
        H("BonaMagaRicheyExtremalFrequency"),
        Blocks(
            Paragraph(Text("Bóna, Maga and Richey, arXiv:2606.06655v2, Section 5.3, page 19: "
                + "“Among all words of a fixed length k, forbidding the word 10^{k-1} or its reversal "
                + "should maximize the frequency rho, although we do not have a proof of this.” "
                + "Section 2 specifies k at least one throughout. Both proposed words and all "
                + "binary competitors of that length are included; constant words are allowed.")),
            Paragraph(Text("A word is a List Bool, with true representing one. The imported "
                + "ForbiddenWordCounting.omega w n consists of every length-n word containing no "
                + "contiguous occurrence of w. Its native rho w n is the total number of ones "
                + "in those words divided by n times their cardinality, with real coercions "
                + "and real division. At n=0 this quotient is totalized; the value at zero "
                + "does not affect convergence atTop. These are Definitions 2.1 and 2.4 of the source. "
                + "The stopped first-hit statistic q is outside this assertion.")),
            Describe.Lean(DescribeId.Create("proposed-word"),
                DeclarationHandle.Create(Prefix + "proposedWord"), H("The proposed word"),
                StatementSource.FromAuthor(Disp(All("k", N(),
                    Equal(Call("proposedWord", F.Id("k")),
                        Qualified("List", "cons", F.Id("true"),
                            Qualified("List", "replicate", Subtract(F.Id("k"), Num(1)), F.Id("false"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural k, proposedWord k is true followed by "
                    + "k-1 copies of false. Subtraction is truncated natural subtraction. The "
                    + "claim uses only k at least one, where this is exactly the length-k word "
                    + "10^{k-1}. The second proposed optimizer is its List.reverse."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("maximizes-frequency"),
                DeclarationHandle.Create(Prefix + "MaximizesFrequency"), H("Maximization of actual limits"),
                StatementSource.FromAuthor(Disp(All("k", N(), All("u", Word(),
                    IffF(Call("MaximizesFrequency", F.Id("k"), F.Id("u")),
                        And(Equal(Length(F.Id("u")), F.Id("k")),
                            Ex("r", R(), And(Limit(F.Id("u"), F.Id("r")),
                                All("v", Word(), Imp(Equal(Length(F.Id("v")), F.Id("k")),
                                    Ex("s", R(), And(Limit(F.Id("v"), F.Id("s")),
                                        LeqF(F.Id("s"), F.Id("r")))))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural k and every binary list u, "
                    + "MaximizesFrequency k u says that u has length k and there exists a real r "
                    + "to which its native rho converges. For every binary list v of length k "
                    + "there must exist a real s to which its native rho converges, with s at most r. "
                    + "The quantified values are actual limits. Uniqueness of real limits makes "
                    + "their choice immaterial. Convergence is part of the assertion, rather than "
                    + "an implication whose convergence premises can be empty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The full universal assertion"),
                StatementSource.FromAuthor(Disp(IffF(F.Id("claim"),
                    All("k", N(), Imp(LeqF(Num(1), F.Id("k")),
                        And(Call("MaximizesFrequency", F.Id("k"), Proposed(F.Id("k"))),
                            Call("MaximizesFrequency", F.Id("k"),
                                Qualified("List", "reverse", Proposed(F.Id("k")))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("claim has type Prop. For every natural k at least one, "
                    + "both the proposed word and its reversal must maximize the limiting "
                    + "frequency among all length-k binary words. There is no restriction on "
                    + "composition, nonconstancy or irreducibility. The separate fixed-composition "
                    + "question later in Section 5.3 is not included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("The universal assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At k=1, proposedWord 1 and its reversal are both [true]. "
                    + "The native theorem BalancedBordersHalfFrequency.rho_singleton gives "
                    + "rho [true] n=0 and rho [false] n=1 for every natural n greater than zero. "
                    + "An eventually constant sequence converges to that constant, so the two "
                    + "actual limits are zero and one, with 0<1. In particular each proposed "
                    + "optimizer has a strictly smaller limiting frequency than the competitor "
                    + "[false] of the same length. The private singleton_tendsto lemma transfers "
                    + "the positive-length native identities to these limits. If claim held, "
                    + "its first maximization at k=1 would give a candidate limit r and a "
                    + "competitor limit s with s≤r. Uniqueness of limits forces r=0 and s=1, "
                    + "contradicting 0<1. The theorem has literal type Not claim. "
                    + "This decides the unrestricted universal assertion. Variants with k at "
                    + "least two, k at least three or only nonconstant words remain unproved here; "
                    + "no general classification of maximizers follows."))), DescribeRole.Theorem))));

    private static Formula Word() => Call("List", F.Id("Bool"));
    private static Formula N() => F.Id("Nat");
    private static Formula R() => F.Id("Real");
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.And, Paren(b));
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        Call(owner + "." + name, args);
    private static Formula Length(Formula w) => Qualified("List", "length", w);
    private static Formula Proposed(Formula k) => Call("proposedWord", k);
    private static Formula Limit(Formula w, Formula r) =>
        Call("Tendsto", Call("rho", w), F.Id("atTop"), Call("nhds", r));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula IffF(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.Iff, Paren(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.Implies, Paren(b));
    private static Formula LeqF(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
